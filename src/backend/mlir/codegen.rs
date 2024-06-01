use std::{
    cell::RefCell,
    collections::{BTreeMap, HashMap},
};

use anyhow::{bail, Result};

use melior::{
    dialect::{
        arith,
        func::{self},
        index,
        llvm::{self, attributes::Linkage},
        memref, scf, DialectRegistry,
    },
    ir::{
        attribute::{
            DenseI64ArrayAttribute, FlatSymbolRefAttribute, IntegerAttribute, StringAttribute,
            TypeAttribute,
        },
        operation::OperationBuilder,
        r#type::{FunctionType, IntegerType, MemRefType},
        Attribute, Block, Identifier, Location, Module, Operation, OperationRef, Region, Type,
        Value, ValueLike,
    },
    pass,
    utility::{register_all_dialects, register_all_llvm_translations},
    Context, ExecutionEngine,
};

use crate::{
    ast::{identifiers::FunctionDeclarationID, nodes::AccessModes},
    control_flow_graph::ControlFlowGraph,
    ir::{self, BlockId, FunctionId, IrProgram},
};

use crate::ast::nodes;
use crate::ast::nodes::FunctionKeyword;
use crate::ast::NodeDatabase;
use crate::ir::Instruction;
use crate::ir::SSAID;

pub fn generate_mlir<'c>(ast: IrProgram ,emit_mlir: bool) -> Result<ExecutionEngine> {
    let registry = DialectRegistry::new();
    register_all_dialects(&registry);

    let context = Context::new();
    context.append_dialect_registry(&registry);
    context.load_all_available_dialects();
    register_all_llvm_translations(&context);

    context.attach_diagnostic_handler(|diagnostic| {
        eprintln!("{}", diagnostic);
        true
    });

    let mut module = Module::new(melior::ir::Location::unknown(&context));
    let code_gen = Box::new(CodeGen::new(
        &context,
        &module,
        HashMap::new(),
        ast.node_db.clone()
    ));
    let code_gen = Box::leak(code_gen);

    code_gen.gen_code(ast)?;

    let pass_manager = pass::PassManager::new(&code_gen.context);
    pass_manager.add_pass(pass::conversion::create_func_to_llvm());

    pass_manager
        .nested_under("func.func")
        .add_pass(pass::conversion::create_arith_to_llvm());
    pass_manager
        .nested_under("func.func")
        .add_pass(pass::conversion::create_index_to_llvm());
    pass_manager.add_pass(pass::conversion::create_scf_to_control_flow());
    pass_manager.add_pass(pass::conversion::create_control_flow_to_llvm());
    pass_manager.add_pass(pass::conversion::create_finalize_mem_ref_to_llvm());
    pass_manager.add_pass(pass::conversion::create_index_to_llvm());
    pass_manager.add_pass(pass::conversion::create_reconcile_unrealized_casts());

    pass_manager.run(&mut module)?;

    if !emit_mlir {
        assert!(module.as_operation().verify());
    }

    if emit_mlir {
        println!("{}", module.as_operation());
    }

    let engine = ExecutionEngine::new(&module, 0, &[], true);

    Ok(engine)
}

struct CodeGen<'ctx, 'module> {
    context: &'ctx Context,
    module: &'module Module<'ctx>,
    annon_string_counter: RefCell<usize>,
    node_db: NodeDatabase,
    type_store: HashMap<SSAID, nodes::Type>,
}

impl<'ctx, 'module> CodeGen<'ctx, 'module> {
    
    fn new(
        context: &'ctx Context,
        module: &'module Module<'ctx>,
        types: HashMap<SSAID, nodes::Type>,
        node_db: NodeDatabase,
    ) -> Self {
        Self {
            context,
            module,
            annon_string_counter: 0.into(),
            type_store: types,
            node_db
        }
    }

    fn gen_code(&self, program: IrProgram) ->  Result<()> {

        for (function_decl_id, cfg) in program.control_flow_graphs {
           let decl = self.gen_function(function_decl_id, cfg, &program.blocks)?;
           self.module.body().append_operation(decl);
        }

        Ok(())
        
    }


    fn gen_function(
        &self,
        function_decl_id: FunctionDeclarationID,
        cfg: ControlFlowGraph<BlockId>,
        block_db: &BTreeMap<BlockId, ir::Block>,
    ) -> Result<(Operation)> {
        let location = melior::ir::Location::unknown(self.context);
        let function_declaration = self
            .node_db
            .function_declarations
            .get(&function_decl_id)
            .unwrap();

        let function_argument_types = function_declaration
            .arguments
            .iter()
            .map(|arg_type| {
                arg_type
                    .r#type.as_ref()
                    .unwrap()
                    .as_mlir_type(self.context, &HashMap::new())
            })
            .collect::<Vec<Type<'ctx>>>();

        let mut function_variable_store: HashMap<SSAID, Value<'ctx, '_>> = HashMap::new();
        let mut current_block = Block::new(
            function_argument_types
                .clone()
                .into_iter()
                .map(|arg_type| (arg_type, location))
                .collect::<Vec<(Type, Location)>>()
                .as_slice(),
        );

        let function_region = Region::new();


        for block_ids in cfg.cycle_aware_successors(&cfg.entry_point)? {
            for block_id in block_ids {
                let block = block_db.get(&block_id).unwrap();

                for instruction in block.instructions.iter() {
                    match instruction {
                        Instruction::Assign(ref lhs_id, ref rhs_id) => {
                            self.gen_assignment(
                                lhs_id,
                                rhs_id,
                                &current_block,
                                &mut function_variable_store,
                            )?;
                        }
                        // TODO: This will need to moved to a separate function when implementing return values;
                        Instruction::Call(function_id, arguments) => {
                            let do_something_with_this = self.gen_function_call(function_id.clone(), arguments.clone(), &mut function_variable_store, &current_block)?;
                        }
                        _ => panic!("instruction not implemented yet"),
                    }
                }
            }
        }
                current_block
                    .append_operation(melior::dialect::func::r#return(&vec![], location));

        function_region.append_block(current_block);

        let function_identifier = function_declaration.identifier.0.clone();
        let return_type = function_declaration.return_type.as_ref().unwrap_or(&nodes::Type::Unit);


        let function_decl = if &function_identifier == "main" {
            func::func(
                &self.context,
                StringAttribute::new(&self.context, &function_identifier),
                TypeAttribute::new(
                    FunctionType::new(
                        &self.context,
                        function_argument_types
                            .iter()
                            .map(|_| llvm::r#type::opaque_pointer(&self.context).into())
                            .collect::<Vec<Type>>()
                            .as_slice(),
                        &[],
                    )
                    .into(),
                ),
                function_region,
                &[(
                    Identifier::new(&self.context, "llvm.emit_c_interface"),
                    Attribute::unit(&self.context),
                )],
                location,
            )
        } else if function_declaration.keywords.contains(&FunctionKeyword::LlvmExtern) {
            llvm::func(
                &self.context,
                StringAttribute::new(&self.context, &function_identifier),
                TypeAttribute::new(
                    llvm::r#type::function(
                        return_type.as_mlir_type(&self.context, &HashMap::new()),
                        function_argument_types
                            .as_slice(),
                        false,
                    )
                    .into(),
                ),
                function_region,
                &[
                    (
                        Identifier::new(&self.context, "sym_visibility"),
                        StringAttribute::new(&self.context, "private").into(),
                    ),
                    (
                        Identifier::new(&self.context, "llvm.emit_c_interface"),
                        Attribute::unit(&self.context),
                    ),
                ],
                location,
            )
        } else {
            func::func(
                &self.context,
                StringAttribute::new(&self.context, &function_identifier),
                TypeAttribute::new(
                    FunctionType::new(
                        &self.context,
                        &function_argument_types,
                        &[return_type.as_mlir_type(&self.context, &HashMap::new())],
                    )
                    .into(),
                ),
                function_region,
                &[],
                location,
            )
        };

        Ok(function_decl)
    }

    fn gen_function_call<'a>(
        &self,
        function_id: FunctionId,
        arguments: Vec<(SSAID, AccessModes)>,
        variable_store: &mut HashMap<SSAID, Value<'ctx, 'a>>,
        current_block: &'a Block<'ctx>,
    ) -> Result<Option<Value<'ctx, 'a>>> {
        let argument_values = arguments
            .iter()
            .map(|arg_id| variable_store.get(&arg_id.0).unwrap().clone())
            .collect::<Vec<Value>>();

        let function_declaration = self
            .node_db
            .function_declarations
            .get(&function_id.0)
            .unwrap();

        let return_type = function_declaration.return_type.as_ref().unwrap_or(&nodes::Type::Unit);
        
        let location = melior::ir::Location::unknown(self.context);

        let call_operation = if function_declaration
            .keywords
            .contains(&FunctionKeyword::LlvmExtern)
        {
            OperationBuilder::new("func.call", location)
                .add_operands(&argument_values)
                .add_attributes(&[(
                    Identifier::new(&self.context, "callee"),
                        FlatSymbolRefAttribute::new(&self.context, &function_declaration.identifier.0).into(),
                )])
                .add_results(&[return_type.as_mlir_type(self.context, &HashMap::new())])
                .build()?
        } else {
            let return_types = if let nodes::Type::Unit = return_type {
                Vec::new()
            } else {
                vec![return_type.as_mlir_type(self.context, &HashMap::new())]
                };

            func::call(
                &self.context,
                FlatSymbolRefAttribute::new(&self.context, &function_declaration.identifier.0),
                &argument_values,
                &return_types,
                location,
            )
        };

        if let Ok(val) = current_block.append_operation(call_operation).result(0) {
            Ok(Some(val.into()))
        } else {
            Ok(None)
        }
    }

    fn gen_assignment<'a>(
        &self,
        lhs_id: &SSAID,
        rhs_id: &SSAID,
        current_block: &'a Block<'ctx>,
        variable_store: &mut HashMap<SSAID, Value<'ctx, 'a>>,
    ) -> Result<()> {
        let initial_value = variable_store.get(rhs_id).unwrap();

        let ptr = melior::dialect::memref::alloca(
            self.context,
            MemRefType::new(initial_value.r#type(), &[], None, None),
            &[],
            &[],
            None,
            Location::unknown(self.context),
        );
        let ptr_val = current_block.append_operation(ptr).result(0).unwrap();
        let store_op = melior::dialect::memref::store(
            *initial_value,
            ptr_val.into(),
            &[],
            melior::ir::Location::unknown(self.context),
        );

        current_block.append_operation(store_op);

        variable_store.insert(*lhs_id, ptr_val.into());

        Ok(())
    }
}



#[cfg(test)]
mod test {
    use super::*;
    use anyhow::Result;
    use rstest::rstest;
    use std::path::PathBuf;

    // NEXT actual: aligns types added outside of this file

    #[rstest]
    fn test_ir_output(#[files("./ir_test_programs/test_*.ts")] path: PathBuf) -> Result<()> {
        use crate::compiler::produce_ir;

        let ir_progam = produce_ir(path.to_str().unwrap())?;
        generate_mlir(ir_progam, true)?;
        panic!();

        Ok(())
    }

}