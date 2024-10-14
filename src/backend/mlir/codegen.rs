use std::{
    cell::RefCell,
    collections::{BTreeMap, HashMap},
};

use tracing::debug;

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
    pass::{self, PassManager},
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

pub struct MlirGenerationConfig {
    pub program: IrProgram,
    pub verify_mlir: bool,
}

// TODO: Figure out how we can share the module generation code without dropping references.

pub fn generate_mlir<'c>(config: MlirGenerationConfig) -> Result<ExecutionEngine> {
    let context = prepare_mlir_context();
    let mut module = Module::new(melior::ir::Location::unknown(&context));
    let code_gen = Box::new(CodeGen::new(
        &context,
        &module,
        HashMap::new(),
        config.program,
    ));
    let code_gen = Box::leak(code_gen);

    code_gen.gen_code()?;

    run_mlir_passes(&context, &mut module);

    if config.verify_mlir {
        assert!(module.as_operation().verify());
    }

    let engine = ExecutionEngine::new(&module, 0, &[], true);

    Ok(engine)
}

fn prepare_mlir_context() -> Context {
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

    context
}

fn run_mlir_passes(context: &Context, module: &mut Module) {
    let pass_manager = pass::PassManager::new(context);
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

    debug!("MLIR output: {}", module.as_operation());
    pass_manager.run(module).unwrap();
}

pub fn generate_mlir_string(cfg: MlirGenerationConfig) -> Result<String> {
    let context = prepare_mlir_context();
    let mut module = Module::new(melior::ir::Location::unknown(&context));
    let code_gen = Box::new(CodeGen::new(&context, &module, HashMap::new(), cfg.program));
    code_gen.gen_code()?;
    run_mlir_passes(&context, &mut module);

    if cfg.verify_mlir {
        assert!(module.as_operation().verify());
    }
    Ok(format!("{}", module.as_operation()))
}

// TODO: move this into a struct with context

struct CodeGen<'ctx, 'module> {
    context: &'ctx Context,
    module: &'module Module<'ctx>,
    annon_string_counter: RefCell<usize>,
    type_store: HashMap<SSAID, nodes::Type>,
    program: IrProgram,
}

impl<'ctx, 'module> CodeGen<'ctx, 'module> {
    fn new(
        context: &'ctx Context,
        module: &'module Module<'ctx>,
        types: HashMap<SSAID, nodes::Type>,
        ir_program: IrProgram,
    ) -> Self {
        Self {
            context,
            module,
            annon_string_counter: 0.into(),
            type_store: types,
            program: ir_program,
        }
    }

    fn gen_code(&self) -> Result<()> {
        debug!("generating code");

        for function_decl_id in self.program.external_function_declaraitons.iter() {
            let decl = self.declare_function(function_decl_id)?;
            self.module.body().append_operation(decl);
        }

        for (function_decl_id, cfg) in self.program.control_flow_graphs.iter() {
            let decl = self.gen_function(function_decl_id, cfg, &self.program.blocks)?;
            self.module.body().append_operation(decl);
        }

        Ok(())
    }

    fn declare_function(&self, function_decl_id: &FunctionDeclarationID) -> Result<Operation> {
        let function_declaration = self
            .program
            .node_db
            .function_declarations
            .get(&function_decl_id)
            .unwrap();

        let argument_types = function_declaration
            .argument_types()
            .map(|r#type| r#type.as_mlir_type(self.context, &HashMap::new()))
            .collect::<Vec<Type<'ctx>>>();
        let function_region = Region::new();
        let location = melior::ir::Location::unknown(self.context);

        if function_declaration.is_external() {
            Ok(llvm::func(
                &self.context,
                StringAttribute::new(&self.context, &function_declaration.identifier.0),
                TypeAttribute::new(
                    llvm::r#type::function(
                        function_declaration
                            .get_return_type()
                            .as_mlir_type(&self.context, &HashMap::new()),
                        argument_types.as_slice(),
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
            ))
        } else {
            bail!("Function declaration is not external")
        }
    }

    fn gen_function(
        &self,
        function_decl_id: &FunctionDeclarationID,
        cfg: &ControlFlowGraph<BlockId>,
        block_db: &BTreeMap<BlockId, ir::Block>,
    ) -> Result<(Operation)> {
        debug!("generating function: {function_decl_id:?}");
        let location = melior::ir::Location::unknown(self.context);
        let function_declaration = self
            .program
            .node_db
            .function_declarations
            .get(&function_decl_id)
            .unwrap();

        let function_argument_types = function_declaration
            .arguments
            .iter()
            .map(|arg_type| {
                arg_type
                    .r#type
                    .as_ref()
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
            let mut block_ids_with_entry: Vec<BlockId> = vec![cfg.entry_point];
            block_ids_with_entry.append(&mut block_ids.clone());
            for block_id in block_ids_with_entry.iter() {
                let block = block_db.get(&block_id).unwrap();
                debug!("generating code for block {}", block_id);

                for instruction in block.instructions.iter() {
                    self.gen_instruction(
                        instruction,
                        &current_block,
                        &current_block, // TODO: is this always the correct entry block?
                        &mut function_variable_store,
                    )?;
                }
            }
        }

        function_region.append_block(current_block);

        let function_identifier = function_declaration.identifier.0.clone();
        let return_type = function_declaration
            .return_type
            .as_ref()
            .unwrap_or(&nodes::Type::Unit);

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
        } else if function_declaration
            .keywords
            .contains(&FunctionKeyword::LlvmExtern)
        {
            llvm::func(
                &self.context,
                StringAttribute::new(&self.context, &function_identifier),
                TypeAttribute::new(
                    llvm::r#type::function(
                        return_type.as_mlir_type(&self.context, &HashMap::new()),
                        function_argument_types.as_slice(),
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
            let mlir_return_type = if let nodes::Type::Unit = return_type {
                vec![]
            } else {
                vec![return_type.as_mlir_type(&self.context, &HashMap::new())]
            };

            func::func(
                &self.context,
                StringAttribute::new(&self.context, &function_identifier),
                TypeAttribute::new(
                    FunctionType::new(&self.context, &function_argument_types, &mlir_return_type)
                        .into(),
                ),
                function_region,
                &[],
                location,
            )
        };

        Ok(function_decl)
    }

    fn gen_variable_load<'a>(
        &self,
        id: SSAID,
        variable_store: &mut HashMap<SSAID, Value<'ctx, 'a>>,
        current_block: &'a Block<'ctx>,
    ) -> Result<Value<'ctx, 'a>> {
        debug!("generating variabe load for {:?}", id);
        let value = self.query_value(&id, variable_store, current_block)?;
        debug!("found value {:?}", value);
        let location = melior::ir::Location::unknown(self.context);
        let result = current_block
            .append_operation(memref::load(value, &[], location))
            .result(0)?
            .into();

        debug!("found result {:?}", result);

        Ok(result)
    }

    fn gen_function_call<'a>(
        &self,
        function_id: FunctionId,
        arguments: Vec<(SSAID, AccessModes)>,
        variable_store: &mut HashMap<SSAID, Value<'ctx, 'a>>,
        current_block: &'a Block<'ctx>,
        result_receiver: &SSAID,
    ) -> Result<()> {
        let argument_values = arguments
            .iter()
            .map(|arg_id| {
                self.gen_variable_load(arg_id.0, variable_store, current_block)
                    .unwrap()
            })
            .collect::<Vec<Value>>();

        debug!("found function arguments: {:?}", argument_values);

        let function_declaration = self
            .program
            .node_db
            .function_declarations
            .get(&function_id.0)
            .unwrap();

        let return_type = function_declaration
            .return_type
            .as_ref()
            .unwrap_or(&nodes::Type::Unit);

        let location = melior::ir::Location::unknown(self.context);

        let call_operation = if function_declaration
            .keywords
            .contains(&FunctionKeyword::LlvmExtern)
        {
            debug!(
                "generating call operation for extern function {} with return type {:?}",
                function_declaration.identifier.0, return_type
            );
            OperationBuilder::new("func.call", location)
                .add_operands(&argument_values)
                .add_attributes(&[(
                    Identifier::new(&self.context, "callee"),
                    FlatSymbolRefAttribute::new(&self.context, &function_declaration.identifier.0)
                        .into(),
                )])
                .add_results(&[return_type.as_mlir_type(self.context, &HashMap::new())])
                .build()?
        } else {
            debug!(
                "generating call operation for internal function {} with return type {:?}",
                function_declaration.identifier.0, return_type
            );
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
            debug!(
                "storing result {:?} for function {:?} into receiver {:?}",
                val, function_id, result_receiver
            );
            let ptr = melior::dialect::memref::alloca(
                self.context,
                MemRefType::new(val.r#type(), &[], None, None),
                &[],
                &[],
                None,
                Location::unknown(self.context),
            );

            let ptr_val = current_block.append_operation(ptr).result(0).unwrap();
            let store_op = melior::dialect::memref::store(
                val.into(),
                ptr_val.into(),
                &[],
                melior::ir::Location::unknown(self.context),
            );

            current_block.append_operation(store_op);

            variable_store.insert(*result_receiver, ptr_val.into());
            Ok(())
        } else {
            Ok(())
        }
    }

    fn gen_instruction<'a>(
        &self,
        instruction: &Instruction,
        current_block: &'a Block<'ctx>,
        entry_block: &'a Block<'ctx>,
        variable_store: &mut HashMap<SSAID, Value<'ctx, 'a>>,
    ) -> Result<Option<Value<'ctx, 'a>>> {
        debug!("generating instruction {:?}", instruction);
        let location = melior::ir::Location::unknown(self.context);
        let result = match instruction {
            Instruction::AssignFnArg(id, position) => {
                debug!("declaring function argument {}", position);
                let value_ref = entry_block.argument(*position).expect(&format!(
                    "expected at least {} function arguments for fn",
                    position,
                ));

                let ptr = current_block
                    .append_operation(memref::alloca(
                        self.context,
                        MemRefType::new(value_ref.r#type(), &[], None, None),
                        &[],
                        &[],
                        None,
                        location,
                    ))
                    .result(0)
                    .unwrap();

                current_block.append_operation(memref::store(
                    value_ref.into(),
                    ptr.into(),
                    &[],
                    location,
                ));

                variable_store.insert(*id, ptr.into());
                None
            }
            Instruction::Assign(ref lhs_id, ref rhs_id) => {
                self.gen_assignment(lhs_id, rhs_id, &current_block, variable_store)?;
                None
            }
            Instruction::Call(function_id, arguments, result_reciever) => {
                self.gen_function_call(
                    function_id.clone(),
                    arguments.clone(),
                    variable_store,
                    &current_block,
                    result_reciever,
                )?;

                variable_store.get(result_reciever).cloned()
            }
            Instruction::Return(result) => {
                let return_values = if let Some(expression) = result {
                    let return_value =
                        self.query_value(expression, variable_store, current_block)?;
                    vec![return_value]
                } else {
                    Vec::new()
                };

                current_block.append_operation(melior::dialect::func::r#return(
                    &return_values,
                    Location::unknown(self.context),
                ));
                None
            }
            Instruction::Addition(lhs, rhs, result_reciever) => {
                let first_operand_value =
                    self.gen_variable_load(*lhs, variable_store, current_block)?;
                let second_operand_value =
                    self.gen_variable_load(*rhs, variable_store, current_block)?;
                let operation = melior::dialect::arith::addi(
                    first_operand_value,
                    second_operand_value,
                    location,
                );

                let value = current_block.append_operation(operation).result(0)?;

                let ptr = melior::dialect::memref::alloca(
                    self.context,
                    MemRefType::new(value.r#type(), &[], None, None),
                    &[],
                    &[],
                    None,
                    Location::unknown(self.context),
                );

                let ptr_val = current_block.append_operation(ptr).result(0).unwrap();
                let store_op = melior::dialect::memref::store(
                    value.into(),
                    ptr_val.into(),
                    &[],
                    melior::ir::Location::unknown(self.context),
                );

                current_block.append_operation(store_op);

                variable_store.insert(*result_reciever, ptr_val.into());

                Some(ptr_val.into())
            }
            Instruction::InitArray(items, result_receiver) => {
                let array_len = items.len();
                let item_values = items
                    .into_iter()
                    .map(|item| self.gen_variable_load(*item, variable_store, current_block))
                    .collect::<Result<Vec<Value>>>()?;

                let array_ptr = current_block
                    .append_operation(memref::alloca(
                        self.context,
                        MemRefType::new(
                            item_values[0].r#type().into(),
                            &[array_len as i64],
                            None,
                            None,
                        ),
                        &[],
                        &[],
                        None,
                        location,
                    ))
                    .result(0)
                    .unwrap()
                    .into();

                for (index, item) in item_values.into_iter().enumerate() {
                    let index = current_block
                        .append_operation(melior::dialect::index::constant(
                            self.context,
                            IntegerAttribute::new(
                                index as i64,
                                melior::ir::Type::index(self.context),
                            )
                            .into(),
                            location,
                        ))
                        .result(0)
                        .unwrap();

                    current_block.append_operation(memref::store(
                        item,
                        array_ptr,
                        &[index.into()],
                        location,
                    ));
                }

                let result_ptr = melior::dialect::memref::alloca(
                    self.context,
                    MemRefType::new(array_ptr.r#type(), &[], None, None),
                    &[],
                    &[],
                    None,
                    Location::unknown(self.context),
                );

                let ptr_val: Value = current_block
                    .append_operation(result_ptr)
                    .result(0)
                    .unwrap()
                    .into();

                let store_op = melior::dialect::memref::store(
                    array_ptr,
                    ptr_val,
                    &[],
                    melior::ir::Location::unknown(self.context),
                );
                current_block.append_operation(store_op);
                debug!("init array {:?}", array_ptr);

                variable_store.insert(*result_receiver, ptr_val);

                Some(ptr_val)
            }
            Instruction::ArrayLookup {
                array,
                index,
                result,
            } => {
                let Ok(index_ptr) = self.gen_variable_load(*index, variable_store, current_block)
                else {
                    bail!("failed to find index {}", index.0);
                };

                let Ok(array_ptr) = self.gen_variable_load(*array, variable_store, current_block)
                else {
                    bail!("failed to find array {}", array.0);
                };

                let casted_index = current_block
                    .append_operation(melior::dialect::index::casts(
                        index_ptr,
                        melior::ir::Type::index(self.context),
                        location,
                    ))
                    .result(0)
                    .unwrap();

                let gep_op_2: Value = current_block
                    .append_operation(memref::load(array_ptr, &[casted_index.into()], location))
                    .result(0)
                    .unwrap()
                    .into();

                let result_ptr = melior::dialect::memref::alloca(
                    self.context,
                    MemRefType::new(gep_op_2.r#type(), &[], None, None),
                    &[],
                    &[],
                    None,
                    Location::unknown(self.context),
                );

                let ptr_val: Value = current_block
                    .append_operation(result_ptr)
                    .result(0)
                    .unwrap()
                    .into();

                let store_op = melior::dialect::memref::store(
                    gep_op_2,
                    ptr_val,
                    &[],
                    melior::ir::Location::unknown(self.context),
                );
                current_block.append_operation(store_op);

                variable_store.insert(*result, ptr_val);

                Some(ptr_val)
            }
            Instruction::MutBorrow(id)
            | Instruction::MutBorrowEnd(id)
            | Instruction::BorrowEnd(id)
            | Instruction::Move(id)
            | Instruction::Borrow(id)
            | Instruction::Drop(id) => None,
            _ => panic!("instruction not implemented yet {:?}", instruction),
        };

        Ok(result)
    }

    fn query_value<'a>(
        &self,
        id: &SSAID,
        variable_store: &mut HashMap<SSAID, Value<'ctx, 'a>>,
        current_block: &'a Block<'ctx>,
    ) -> Result<Value<'ctx, 'a>> {
        debug!("querying value {:?}", id);
        if let Some(value) = variable_store.get(id) {
            debug!("value type {:?}", value);
            return Ok(value.clone());
        }

        debug!("found static value");
        if let Some(static_value) = self.program.static_values.get(id) {
            match static_value {
                nodes::Value::String(val) => {
                    // TODO: \n is getting escaped, perhap we need a raw string?
                    let val = if val == "\\n" { "\n" } else { &val };
                    let val = val.replace("\\n", "\n");

                    let value: Value = self
                        .gen_pointer_to_annon_str(current_block, val.to_string())?
                        .result(0)?
                        .into();

                    let ptr = melior::dialect::memref::alloca(
                        self.context,
                        MemRefType::new(value.r#type(), &[], None, None),
                        &[],
                        &[],
                        None,
                        Location::unknown(self.context),
                    );

                    let ptr_val = current_block.append_operation(ptr).result(0).unwrap();
                    let store_op = melior::dialect::memref::store(
                        value,
                        ptr_val.into(),
                        &[],
                        melior::ir::Location::unknown(self.context),
                    );

                    current_block.append_operation(store_op);

                    variable_store.insert(*id, ptr_val.into());
                    return Ok(ptr_val.into());
                }
                nodes::Value::Integer(value) => {
                    let integer_val: Value = current_block
                        .append_operation(melior::dialect::arith::constant(
                            &self.context,
                            IntegerAttribute::new(
                                value.value as i64, // TODO why do we need 4 here?
                                IntegerType::new(&self.context, 32).into(),
                            )
                            .into(),
                            Location::unknown(self.context),
                        ))
                        .result(0)?
                        .into();

                    let ptr = melior::dialect::memref::alloca(
                        self.context,
                        MemRefType::new(integer_val.r#type(), &[], None, None),
                        &[],
                        &[],
                        None,
                        Location::unknown(self.context),
                    );

                    let ptr_val = current_block.append_operation(ptr).result(0).unwrap();

                    let store_op = melior::dialect::memref::store(
                        integer_val.into(),
                        ptr_val.into(),
                        &[],
                        melior::ir::Location::unknown(self.context),
                    );
                    current_block.append_operation(store_op);

                    variable_store.insert(*id, ptr_val.into());

                    return Ok(ptr_val.into());
                }
                _ => panic!(),
            }
        } else {
            panic!(
                "failed to find ssaid: {}",
                self.program
                    .ssa_variables
                    .get(id)
                    .unwrap()
                    .original_variable
                    .0
            );
        }
    }

    pub fn gen_pointer_to_annon_str<'a>(
        &self,
        current_block: &'a Block<'ctx>,
        value: String,
    ) -> Result<OperationRef<'ctx, 'a>> {
        self.generate_annon_string(value, current_block)
    }
    fn gen_annon_string_id(&self) -> String {
        let id = format!("annonstr{}", self.annon_string_counter.borrow());

        self.annon_string_counter
            .replace_with(|&mut v| v + 1 as usize);

        id
    }

    fn generate_annon_string<'a>(
        &self,
        value: String,
        current_block: &'a Block<'ctx>,
    ) -> Result<OperationRef<'ctx, 'a>> {
        let location = melior::ir::Location::unknown(self.context);
        let id = self.gen_annon_string_id();
        let string_type = llvm::r#type::array(
            IntegerType::new(&self.context, 8).into(),
            (value.len()) as u32,
        );
        let op = OperationBuilder::new("llvm.mlir.global", location)
            .add_regions([Region::new()])
            .add_attributes(&[
                (
                    Identifier::new(&self.context, "value"),
                    StringAttribute::new(&self.context, &format!("{value}")).into(),
                ),
                (
                    Identifier::new(&self.context, "sym_name"),
                    StringAttribute::new(&self.context, &id).into(),
                ),
                (
                    Identifier::new(&self.context, "global_type"),
                    TypeAttribute::new(string_type).into(),
                ),
                (
                    Identifier::new(&self.context, "linkage"),
                    llvm::attributes::linkage(&self.context, Linkage::Internal),
                ),
            ])
            .build()?;

        self.module.body().append_operation(op);

        let address_op = OperationBuilder::new("llvm.mlir.addressof", location)
            // .enable_result_type_inference()
            .add_attributes(&[(
                Identifier::new(&self.context, "global_name"),
                FlatSymbolRefAttribute::new(&self.context, &id).into(),
            )])
            .add_results(&[llvm::r#type::opaque_pointer(&self.context)])
            .build()?;

        Ok(current_block.append_operation(address_op))
    }

    fn gen_assignment<'a>(
        &self,
        lhs_id: &SSAID,
        rhs_id: &SSAID,
        current_block: &'a Block<'ctx>,
        variable_store: &mut HashMap<SSAID, Value<'ctx, 'a>>,
    ) -> Result<()> {
        debug!("generating assignment");
        let initial_value = self.query_value(rhs_id, variable_store, current_block)?;
        debug!("found initial value");

        variable_store.insert(*lhs_id, initial_value);

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use anyhow::Result;
    use rstest::rstest;
    use std::path::PathBuf;

    #[rstest]
    #[test_log::test]
    fn test_ir_output(#[files("./ir_test_programs/test_*.ts")] path: PathBuf) -> Result<()> {
        use crate::compiler::produce_ir;

        let ir_program = produce_ir(path.to_str().unwrap())?;
        let mlir_generation_config = MlirGenerationConfig {
            verify_mlir: true,
            program: ir_program.clone(),
        };

        debug!("testing codegen for IR: {ir_program}");
        let mlir_output = generate_mlir_string(mlir_generation_config)?;

        insta::assert_snapshot!(
            format!(
                "test_well_formed_ir_{}",
                path.file_name().unwrap().to_str().unwrap()
            ),
            format!("{}", mlir_output)
        );

        Ok(())
    }
}
