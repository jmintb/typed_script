use std::{
    cell::{Cell, RefCell, Ref},
    collections::{BTreeMap, HashMap},
    rc::Rc
};

use tracing::debug;

use anyhow::{bail, Result};



use melior::{
    dialect::{
        arith,
        func::{self},
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
        Value, ValueLike, BlockRef,
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
use crate::ir::Instruction;
use crate::ir::SSAID;
use crate::analysis::type_evaluation::IrProgramTypes;

pub struct MlirGenerationConfig {
    pub program: IrProgram,
    pub verify_mlir: bool,
    pub program_types: BTreeMap<FunctionDeclarationID, IrProgramTypes>,
}

// TODO: Figure out how we can share the module generation code without dropping references.

pub fn generate_mlir<'c>(config: MlirGenerationConfig) -> Result<ExecutionEngine> {
    let context = prepare_mlir_context();
    let mut module = Module::new(melior::ir::Location::unknown(&context));
    let mut code_gen = Box::new(CodeGen::new(
        &context,
        &module,
        HashMap::new(),
        config.program,
        config.program_types
    ));

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
    let mut code_gen = Box::new(CodeGen::new(&context, &module, HashMap::new(), cfg.program, cfg.program_types));
    code_gen.gen_code()?;
    run_mlir_passes(&context, &mut module);

    if cfg.verify_mlir {
        assert!(module.as_operation().verify());
    }
    Ok(format!("{}", module.as_operation()))
}

use crate::types;

    pub fn as_mlir_type<'c, 'a>(fusion_type: types::Type, context: &'c Context, types: &IrProgramTypes) -> melior::ir::Type<'a> where 'c: 'a {
        match fusion_type {
            types::Type::Pointer => llvm::r#type::opaque_pointer(context),
            types::Type::String => llvm::r#type::opaque_pointer(context),
            types::Type::Integer(_) => IntegerType::new(context, 32).into(),
            types::Type::Boolean => IntegerType::new(context, 1).into(),
            types::Type::Unit => llvm::r#type::void(context),
            types::Type::Array(array_type_id) => {

                            let array_type = types.array_types.get(array_type_id).unwrap();
                            let element_type = as_mlir_type(array_type.element_type, context, types);
                            

                            MemRefType::new(
                                element_type,
                                &[array_type.length as i64],
                                None,
                                None,
                                ).into()
            }
            _ => todo!("unimplemented type to mlir type {:?}", fusion_type),
        }
    }
    
pub fn as_memref_type<'c, 'a>(fusion_type: types::Type, context: &'c Context, types: &IrProgramTypes) -> MemRefType<'a> where 'c: 'a {
        match fusion_type {
            types::Type::Array(array_type_id) => {

                            let array_type = types.array_types.get(array_type_id).unwrap();
                            let element_type = as_mlir_type(array_type.element_type, context, types);
                            

                            MemRefType::new(
                                element_type,
                                &[array_type.length as i64],
                                None,
                                None,
                                )
            }
            _ => todo!("unimplemented type to memref type {:?}", fusion_type),
        }
    }

struct MlirFunctionStructure<'c, 'a> {
    regions: HashMap<BlockId, Region<'c>>,
    block_references: HashMap<usize, BlockRef<'c,'a>>,
    function_region: Region<'c>
}


    
    struct EntityMap<Entity> {
         entities: Vec<Entity>
    }

impl<Entity> EntityMap<Entity>
{
    fn new() -> Self {
        Self {
            entities: Vec::new()
        }
    }

    fn append(&mut self, entity: Entity) {
        self.entities.push(entity);
    }
}


// TODO: move this into a struct with context

struct CodeGen<'ctx> {
    context: &'ctx Context,
    module: &'ctx Module<'ctx>,
    annon_string_counter: RefCell<usize>,
    type_store: HashMap<SSAID, nodes::Type>,
    program: IrProgram,
    program_types: BTreeMap<FunctionDeclarationID, IrProgramTypes>,
    current_fn_decl_id: FunctionDeclarationID
}

impl<'ctx> CodeGen<'ctx> {
    fn new(
        context: &'ctx Context,
        module: &'ctx Module<'ctx>,
        types: HashMap<SSAID, nodes::Type>,
        ir_program: IrProgram,
        ir_types: BTreeMap<FunctionDeclarationID, IrProgramTypes>
    ) -> Self {
        Self {
            context,
            module,
            annon_string_counter: 0.into(),
            type_store: types,
            current_fn_decl_id: ir_program.entry_function_id,
            program: ir_program,
            program_types: ir_types,

        }
    }

    fn gen_code<'a> (&'a mut self) -> Result<()> {
        debug!("generating code");

        for function_decl_id in self.program.external_function_declaraitons.iter() {
            let decl = self.declare_function(function_decl_id)?;
            self.module.body().append_operation(decl);
        }

        for (function_decl_id, cfg) in self.program.control_flow_graphs.iter() {
            self.current_fn_decl_id = *function_decl_id;
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

    fn gen_locals<'c, 'a>(
        &self,
        entry_block: &'c BlockRef<'c, 'a>,
        function_decl_id: &FunctionDeclarationID,
    ) -> HashMap<SSAID, Value<'c, 'a>> where 'ctx: 'c {
        let mut locals = HashMap::<SSAID, Value<'c, 'a>>::new();
        let local_ir_variables = &self.program.ssa_variables[function_decl_id];

        for (ssa_id, value) in local_ir_variables {

            let fusion_type = if self.program.ssa_variable_types.contains_key(ssa_id) { 
                self.program.ssa_variable_types.get(ssa_id).expect(&format!("failed to find type for: {:?}", ssa_id))
            } else {
                self.program_types.get(function_decl_id).unwrap().variable_types.get(ssa_id).unwrap()
            };



            debug!("found type {:?} for ssa id {:?}", fusion_type, ssa_id);
            let inner_type = as_mlir_type(fusion_type.clone(),self.context, self.program_types.get(function_decl_id).unwrap());
            let variable_allocation_op = melior::dialect::memref::alloca(
                self.context,
                MemRefType::new(inner_type, &[], None, None),
                &[],
                &[],
                None,
                Location::unknown(self.context),
            );
            let variable_mlir_value: Value = entry_block.append_operation(variable_allocation_op).result(0).unwrap().into();
            locals.insert(*ssa_id, variable_mlir_value);

            /*

            if let types::Type::Array(_) = fusion_type {
            }
            */

            let key = ssa_id;
            if self.program.static_values.contains_key(key) {
                let value = &self.program.static_values[key];
            let ptr = locals.get(key).unwrap();

            match value {
                nodes::Value::Integer(int) => {

                    let integer_val: Value = entry_block.append_operation(melior::dialect::arith::constant(
                            &self.context,
                            IntegerAttribute::new(
                                int.value as i64, // TODO why do we need 4 here?
                                IntegerType::new(&self.context, 32).into(),
                            )
                            .into(),
                            Location::unknown(self.context),
                        ))
                        .result(0).unwrap()
                        .into();


                let store_op = melior::dialect::memref::store(
                    integer_val,
                    *ptr,
                    &[],
                    melior::ir::Location::unknown(self.context),
                    );

                entry_block.append_operation(store_op);
                    
                }

                nodes::Value::String(val) => {
                    // TODO: \n is getting escaped, perhap we need a raw string?
                    let val = if val == "\\n" { "\n" } else { &val };
                    let val = val.replace("\\n", "\n");

                    let value: Value = self
                        .gen_pointer_to_annon_str(entry_block, val.to_string()).unwrap()
                        .result(0).unwrap()
                        .into();

                    let store_op = melior::dialect::memref::store(
                        value,
                       *ptr,
                        &[],
                        melior::ir::Location::unknown(self.context),
                    );

                    entry_block.append_operation(store_op);

                    // MOVE: this to locals calculation
                    // variable_store.insert(*id, ptr_val.into());
                }
                _ => todo!("expected static value found {:?}", value)
            }

        }

            }




        locals
    }

    fn gen_function(
        &self,
        function_decl_id: &FunctionDeclarationID,
        cfg: &ControlFlowGraph<BlockId>,
        block_db: &BTreeMap<BlockId, ir::Block>,
    ) -> Result<Operation<'_>> {
        debug!("generating function: {function_decl_id:?}");

        let structure = MlirFunctionStructure { regions: HashMap::new(), block_references: HashMap::new(), function_region: Region::new()};

        let mut regions = Rc::new(RefCell::new(self.pre_gen_regions(cfg)?));

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
            .collect::<Vec<Type<'_>>>();

        debug!("creating function entry block with arguments: {}", function_argument_types.len());
        let current_block = Block::new(
            function_argument_types
                .clone()
                .into_iter()
                .map(|arg_type| (arg_type, location))
                .collect::<Vec<(Type, Location)>>()
                .as_slice(),
        );

        let borrow_regions = regions.borrow();

        let result = self.pre_gen_blocks(&cfg, &structure.function_region, &borrow_regions, current_block)?;
        let entry_block_ref = result[&cfg.entry_point.0];
        let local_variable_store = self.gen_locals(&entry_block_ref, function_decl_id);

        // TODO: sort out how to handle entry block and fn args. use first block in region maybe?

            let mut ir_blocks = cfg.cycle_aware_successors(&cfg.entry_point)?;
            ir_blocks.insert(0, vec![cfg.entry_point]);

            debug!("found ir blocks: {:?}, cfg: {:?}", ir_blocks, cfg.entry_point);

        for block_ids in ir_blocks {
            for block_id in block_ids {
            // Should only iterate over "top" level blocks, the rest are generated from inside other instructions.
            // Therefore check for blocks that dominates the entry block or is the entry block it self.
            // I don't thin the domination block is entirely correct yet.
            // Question: When do we need multiple top level blocks?
                debug!("block {:?} dominates entry {:?}", block_id, cfg.dominates3(block_id, cfg.entry_point));
            if cfg.dominates3(block_id, cfg.entry_point) || block_id == cfg.entry_point {
                debug!("generating code for block {}", block_id);
                self.gen_block(block_id, &result, &local_variable_store, block_db, cfg, &vec![local_variable_store.clone()])?;
            }

            }
        }


        let function_region = structure.function_region;
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
                    let mlir_return_type = vec![return_type.as_mlir_type(&self.context, &HashMap::new())];

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


    fn gen_variable_load<'a, 'c>(
        &self,
        id: SSAID,
        block_references: &'a HashMap<usize, BlockRef<'c, 'a>>,
        variable_store: & HashMap<SSAID, Value<'c, 'a>>,
        current_block: usize,
        ) -> Result<Value<'c, 'a>> where 'a: 'c, 'ctx: 'a  {
        debug!("generating variabe load for {:?}", id);
        self.query_value(&id, block_references, variable_store, current_block)?;
        // MOVE; value from query_value function
        let value = variable_store.get(&id).unwrap().to_owned();
        debug!("found value {:?}", value);
        let current_block = block_references.get(&current_block).unwrap();
        let location = melior::ir::Location::unknown(self.context);
        let result: Value = current_block
            .append_operation(memref::load(value, &[], location))
            .result(0)?
            .into();

        debug!("found result {:?}", result);

        Ok(result)
    }
    
    fn gen_resultless_function_call<'a, 'c>(
        &self,
        function_id: FunctionId,
        arguments: Vec<(SSAID, AccessModes)>,
        block_references: &'a HashMap<usize, BlockRef<'c, 'a>>,
        variable_store: &HashMap<SSAID, Value<'c, 'a>>,
        current_block_id: usize,
        ) -> Result<()>  where 'a: 'c, 'ctx: 'a {
        let current_block = block_references.get(&current_block_id).unwrap();
        let argument_values = arguments
            .iter()
            .map(|arg_id| {
                self.gen_variable_load(arg_id.0, block_references, variable_store, current_block_id)
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

        let return_type = &nodes::Type::Unit;

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


            //let ptr_val = current_block.append_operation(ptr).result(0).unwrap();
            /*
            let ptr_val = variable_store[result_receiver];
            let store_op = melior::dialect::memref::store(
                val.into(),
                ptr_val.into(),
                &[],
                melior::ir::Location::unknown(self.context),
                );

            current_block.append_operation(store_op);
            */

            Ok(())
        } else {
            Ok(())
        }
    }

    fn gen_function_call<'a, 'c>(
        &self,
        function_id: FunctionId,
        arguments: Vec<(SSAID, AccessModes)>,
        block_references: &'a HashMap<usize, BlockRef<'c, 'a>>,
        variable_store: &HashMap<SSAID, Value<'c, 'a>>,
        current_block_id: usize,
        result_receiver: &SSAID,
        ) -> Result<()>  where 'a: 'c, 'ctx: 'a {
        let current_block = block_references.get(&current_block_id).unwrap();
        let argument_values = arguments
            .iter()
            .map(|arg_id| {
                self.gen_variable_load(arg_id.0, block_references, variable_store, current_block_id)
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


            //let ptr_val = current_block.append_operation(ptr).result(0).unwrap();
            
            let ptr_val = variable_store[result_receiver];
            let store_op = melior::dialect::memref::store(
                val.into(),
                ptr_val.into(),
                &[],
                melior::ir::Location::unknown(self.context),
                );

            current_block.append_operation(store_op);
            

            Ok(())
        } else {
            Ok(())
        }
    }

    fn pre_gen_regions(&self, cfg: &ControlFlowGraph<BlockId>) -> Result<HashMap<BlockId, Region<'_>>> {

        let mut regions = HashMap::<BlockId, Region<'_>>::new();

        for block_ids in cfg.cycle_aware_successors(&cfg.entry_point)? {
            for block_id in block_ids {
                let ir_block = self.program.blocks.get(&block_id).unwrap();

                // TODO: Not sure if this holds if we have multiple blocks in a conditional region.
                // Maybe we can default to parents region if the block is not a direct child of control flow?
                if ir_block.produced_directly_by_control_flow {
                    let region_for_block = Region::new();
                    regions.insert(block_id, region_for_block);
                } 

            }
        }

        Ok(regions)
    }

    fn pre_gen_blocks<'a, 'c> (& self, cfg: &ControlFlowGraph<BlockId>, function_region: &'a Region<'c>, regions: &'a Ref<'a, HashMap<BlockId, Region<'c>>>, entry_block: Block<'c>) -> Result<HashMap<usize, BlockRef<'c, 'a>>>

    {
        let entry_block_reference = function_region.append_block(entry_block);
        let mut result: HashMap<usize, BlockRef<'c, 'a>> = HashMap::new();
        result.insert(cfg.entry_point.0, entry_block_reference);

        for block_ids in cfg.cycle_aware_successors(&cfg.entry_point)? {
            for block_id in block_ids {
                let block = Block::new(&[]);
                let ir_block = self.program.blocks.get(&block_id).unwrap();

                if !ir_block.produced_directly_by_control_flow {
                    result.insert(block_id.0, entry_block_reference);
                }

            }
        }

        Ok(result)
    }


    // NEXT: Make block generation pull based, using similar method to ir.rs. Where we return the next/current block allowing the generation code to decide what the next block should be.
    // This will allow generating blocks as needed for example in if/else cases.
    fn gen_block<'region, 'context, 'blocks, 'vars, 'varc>(
        &self,
        block_id: BlockId,
        block_references: &'blocks HashMap<usize, BlockRef<'context, 'region>>,
        variable_store: &'vars HashMap<SSAID, Value<'varc, 'region>>,
        block_db: &BTreeMap<BlockId, ir::Block>,
        cfg: &ControlFlowGraph<BlockId>,
        variable_stores: &'vars Vec<HashMap<SSAID, Value<'varc, 'region>>>,
        ) -> Result<()> where 'ctx: 'context, 'blocks: 'context, 'vars: 'context, 'region: 'varc  {
        let ir_block = block_db.get(&block_id).unwrap();
        // TODO: What about block arguments?

        for instruction in ir_block.instructions.iter() {
            self.gen_instruction(
                instruction,
                block_id.0,
                cfg,
                block_references,
                variable_store,
                variable_stores,
                block_db,
                )?;
        }


        Ok(())

    }

    // TODO Next: Need to create a new mutable map of local vars for each operation layer and then provide a set of maps from parent scopes.
    fn generate_if_else_operation<'parent_block, 'parent_context, 'context, 'this>(
        &self, 
        if_block_id: usize,
        else_block_id: usize,
        condition: Value<'parent_context, 'parent_block>, 
        location: Location<'parent_context>,
        cfg: &ControlFlowGraph<BlockId>,
        variable_store: &HashMap<SSAID, Value<'parent_block, 'parent_block>>,
        variable_stores: &'this Vec<HashMap<SSAID, Value<'parent_context, 'parent_block>>>,
        block_db: &BTreeMap<BlockId, ir::Block>,
        ) -> Result<(Operation<'context>)> where 'parent_context: 'this, 'parent_block: 'this, 'parent_context: 'context  {
        debug!("generating if else with blocks {:?}, {:?}", if_block_id, else_block_id);
        let if_block = Block::new(&[]);
        let else_block = Block::new(&[]);

        let if_region = Region::new(); 
        let else_region = Region::new();

        let if_block_ref = if_region.append_block(if_block);
        let else_block_ref = else_region.append_block(else_block);

        let mut block_references: HashMap<usize, BlockRef<'_, '_>> = HashMap::new();
        block_references.insert(if_block_id, if_block_ref);
        block_references.insert(else_block_id, else_block_ref);


        self.gen_block(BlockId(if_block_id), &block_references, variable_store, block_db, cfg, variable_stores )?;
        // TODO: is there a scoping issue here? Could if block interefere with else block.
        self.gen_block(BlockId(else_block_id), &block_references, variable_store, block_db, cfg, variable_stores )?;

        if_block_ref.append_operation(scf::r#yield(&[], location));
        else_block_ref.append_operation(scf::r#yield(&[], location));

        Ok(melior::dialect::scf::r#if(
                condition,
                &[],
                if_region,
                else_region,
                location,
                ))


    }

        fn generate_arith_comparion<'context, 'region>(&self, left_hand_side: SSAID, right_hand_side: SSAID, reciever: SSAID, predicate: arith::CmpiPredicate, block_references: &HashMap<usize, BlockRef<'context, 'region>>, variable_store: & HashMap<SSAID, Value<'context, 'region>>, current_block_id: usize ) -> Result<()> {

                let current_block = block_references.get(&current_block_id).unwrap();
                let location = melior::ir::Location::unknown(self.context);
                let first_operand_value =
                    self.gen_variable_load(left_hand_side, block_references, variable_store, current_block_id)?;
                let second_operand_value =
                    self.gen_variable_load(right_hand_side, block_references, variable_store, current_block_id)?;
                let operation = melior::dialect::arith::cmpi(
                    self.context,
                    predicate,
                    first_operand_value,
                    second_operand_value,
                    location,
                    );

                let value = current_block.append_operation(operation).result(0)?;

                let ptr_val = variable_store[&reciever];
                let store_op = melior::dialect::memref::store(
                    value.into(),
                    ptr_val.into(),
                    &[],
                    melior::ir::Location::unknown(self.context),
                    );

                current_block.append_operation(store_op);

                Ok(())
    }

    fn gen_instruction<'parent_block, 'parent_context, 'context, 'this, 'blocks, 'vars, 'varc>(
        &self,
        instruction: &Instruction,
        current_block_id: usize,
        cfg: &ControlFlowGraph<BlockId>,
        block_references: &'blocks HashMap<usize, BlockRef<'context, 'parent_block>>,
        variable_store: &'vars HashMap<SSAID, Value<'varc, 'this>>,
        variable_stores: &'this Vec<HashMap<SSAID, Value<'parent_context, 'parent_block>>>,
        block_db: &BTreeMap<BlockId, ir::Block>
        ) -> Result<Option<Value<'context, 'parent_block>>> where 'ctx: 'this, 'ctx: 'context, 'this: 'context, 'blocks: 'context, 'blocks: 'vars, 'vars: 'varc, 'varc: 'context  {
        debug!("generating instruction {:?} {:?}", instruction, block_references);
        let current_block = block_references.get(&current_block_id).unwrap();
        let location = melior::ir::Location::unknown(self.context);
        let result = match instruction {
            Instruction::AssignFnArg(id, position) => {
                debug!("declaring function argument {} {}",id.0, position);
                let value_ref = current_block.argument(*position).expect(&format!( // TODO: might need entry block here?
                        "expected at least {} function arguments for fn",
                        position + 1,
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

                // MOVE NEXT: get fn args into variable store.
                let ptr = variable_store[id];


                current_block.append_operation(memref::store(
                        value_ref.into(),
                        ptr.into(),
                        &[],
                        location,
                        ));

                // MOVE: move result reciever init to locals generation.
                // variable_store.insert(*id, ptr.into());
                None
            }
            Instruction::Assign(ref lhs_id, ref rhs_id) => {
                self.gen_assignment(lhs_id, rhs_id, current_block_id, block_references, variable_store)?;
                None
            }
            Instruction::ResultlessCall(function_id, arguments) => {
                
                       self.gen_resultless_function_call(
                       function_id.clone(),
                       arguments.clone(),
                       block_references,
                       variable_store,
                       current_block_id,
                       )?;

                       //variable_store.get(result_reciever).cloned()
                       None
            }
            Instruction::Call(function_id, arguments, result_reciever) => {
                
                       self.gen_function_call(
                       function_id.clone(),
                       arguments.clone(),
                       block_references,
                       variable_store,
                       current_block_id,
                       result_reciever,
                       )?;

                       variable_store.get(result_reciever).cloned()
            }
            Instruction::Return(result) => {
                let return_values = if let Some(expression) = result {
                    let val = self.gen_variable_load(*expression, block_references, variable_store, current_block_id)?;

                    vec![val]
                } else {
                    Vec::new()
                };

                debug!("generating return instruction for block: {}", current_block_id);

                current_block.append_operation(melior::dialect::func::r#return(
                        &return_values,
                        Location::unknown(self.context),
                        ));
                None
            }
            Instruction::Addition(lhs, rhs, result_reciever) => {
                let first_operand_value =
                    self.gen_variable_load(*lhs, block_references, variable_store, current_block_id)?;
                let second_operand_value =
                    self.gen_variable_load(*rhs, block_references, variable_store, current_block_id)?;
                let operation = melior::dialect::arith::addi(
                    first_operand_value,
                    second_operand_value,
                    location,
                    );

                let value = current_block.append_operation(operation).result(0)?;

                let ptr_val = variable_store[result_reciever];

                let store_op = melior::dialect::memref::store(
                    value.into(),
                    ptr_val.into(),
                    &[],
                    melior::ir::Location::unknown(self.context),
                    );

                current_block.append_operation(store_op);

                Some(ptr_val.into())
            }

            Instruction::GreaterThan(lhs, rhs, result_reciever) => {
                self.generate_arith_comparion(*lhs, *rhs, *result_reciever, arith::CmpiPredicate::Sgt, block_references, variable_store, current_block_id)?;
                let ptr_val = variable_store[result_reciever];
                Some(ptr_val.into())
            }
            
            Instruction::LessThan(lhs, rhs, result_reciever) => {
                self.generate_arith_comparion(*lhs, *rhs, *result_reciever, arith::CmpiPredicate::Slt, block_references, variable_store, current_block_id)?;
                let ptr_val = variable_store[result_reciever];
                Some(ptr_val.into())
            }
            Instruction::IfElse(
                condition,
                then_block,
                else_block,
                ) => {
                debug!("generate code for if else" );
                let condition = self.gen_variable_load(*condition, block_references, variable_store, current_block_id)?;

                // let then_mlir_block = block_references.get(&then_block.0).unwrap();
                // let else_mlir_block = block_references.get(&else_block.0).unwrap();

                // block_map.insert(*then_block, then_mlir_block_reference);
                // block_map.insert(*else_block, else_mlir_block_reference);
                // NEXT NEXT: make it so we can just return the next bock_id and have gen_block retrieve the write mlirblockref.
                // How do we get the followup block id here? Find the dominator

                // TODO: what is if/else is the last expression?
                // let next_block = cfg.find_first_common_successor(then_block, else_block).unwrap();

                // TODO: Will we ever need to reuse the 
                // TODO: Next ish check if this architecture can handle scoping -> conclusion it should
                   
                 let if_operation = self.generate_if_else_operation(then_block.0, else_block.0, condition, location, cfg, variable_store, variable_stores, block_db);
                 current_block.append_operation(if_operation?);


                None
            }
            Instruction::InitArray(items, result_receiver) => {
                let array_len = items.len();
                let item_values = items
                    .into_iter()
                    .map(|item| self.gen_variable_load(*item, block_references, variable_store, current_block_id))
                    .collect::<Result<Vec<Value>>>()?;

                let program_types = self.program_types.get(&self.current_fn_decl_id).unwrap();
                let array_type = program_types.variable_types.get(result_receiver).unwrap();
                let memref_type = as_memref_type(*array_type, self.context, program_types);
                            

                let array_ptr = melior::dialect::memref::alloca(
                    self.context,
                    memref_type,
                    &[],
                    &[],
                    None,
                    Location::unknown(self.context)
                    ); 

                let array_ptr_val: Value = current_block
                    .append_operation(array_ptr)
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
                            array_ptr_val,
                            &[index.into()],
                            location,
                            ));
                }


                let ptr_val: Value = variable_store[result_receiver];


                let store_op = melior::dialect::memref::store(
                    array_ptr_val,
                    ptr_val,
                    &[],
                    melior::ir::Location::unknown(self.context),
                    );
                current_block.append_operation(store_op);

                // MOVE: move result reciever init to locals generation.

                // variable_store.insert(*result_receiver, ptr_val);

                Some(ptr_val)
            }
            Instruction::ArrayLookup {
                array,
                index,
                result,
            } => {
                let Ok(index_ptr) = self.gen_variable_load(*index, block_references, variable_store, current_block_id)
                    else {
                        bail!("failed to find index {}", index.0);
                    };

                    let Ok(array_ptr) = self.gen_variable_load(*array, block_references, variable_store, current_block_id)
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

                        let ptr_val: Value = variable_store[result];

                        let store_op = melior::dialect::memref::store(
                            gep_op_2,
                            ptr_val,
                            &[],
                            melior::ir::Location::unknown(self.context),
                );
                current_block.append_operation(store_op);

                // MOVE: move result init to locals calculation
                // variable_store.insert(*result, ptr_val);

                Some(ptr_val)
            }
            Instruction::AnonymousValue(id) => {
                Some(self.gen_variable_load(*id, block_references, variable_store, current_block_id)?)
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

    fn query_value<'parent_block, 'context, 'varc, 'this, 'otherthis>(
        &self,
        id: &SSAID,
        block_references: &'this HashMap<usize, BlockRef<'context, 'parent_block>>,
        variable_store: &'otherthis HashMap<SSAID, Value<'varc, 'parent_block>>,
        current_block: usize,
    ) -> Result<()> where 'ctx: 'context, 'this: 'context, 'ctx: 'varc, 'this: 'varc     {
       
       return Ok(());
        debug!("query value {} in block {} {:?}", id.0, current_block, block_references);
       let current_block = block_references.get(&current_block).unwrap();


       if !self.program.static_values.contains_key(id) {

           return Ok(());
       }

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

                    let ptr_val = current_block.append_operation(ptr).clone().result(0).unwrap();
                    let store_op = melior::dialect::memref::store(
                        value,
                        ptr_val.into(),
                        &[],
                        melior::ir::Location::unknown(self.context),
                    );

                    current_block.append_operation(store_op);

                    // MOVE: this to locals calculation
                    // variable_store.insert(*id, ptr_val.into());
                    return Ok(());
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

                    // let ptr_val = current_block.append_operation(ptr).clone().result(0).unwrap().clone();
                    let ptr_val = current_block.append_operation(ptr).clone().result(0).unwrap();

                    let store_op = melior::dialect::memref::store(
                        integer_val.into(),
                        ptr_val.into(),
                        &[],
                        melior::ir::Location::unknown(self.context),
                    );
                    current_block.append_operation(store_op);

                    // MOVE: move to locals calculation
                    // variable_store.insert(*id, ptr_val.into());

                    return Ok(());
                }

                _ => panic!(),
            }
        } else {
            panic!(
                "failed to find ssaid: {} {}",
                id.0,
                self.program
                    .ssa_variables[&self.current_fn_decl_id]
                    .get(id)
                    .unwrap()
                    .original_variable
                    .0
            );
        }
    }

    pub fn gen_pointer_to_annon_str<'a, 'c>(
        &self,
        current_block: &'a Block<'c>,
        value: String,
    ) -> Result<OperationRef<'c, 'a>> where 'ctx: 'a, 'ctx: 'c {
        self.generate_annon_string(value, current_block)
    }
    fn gen_annon_string_id(&self) -> String {
        let id = format!("annonstr{}", self.annon_string_counter.borrow());

        self.annon_string_counter
            .replace_with(|&mut v| v + 1 as usize);

        id
    }

    fn generate_annon_string<'a, 'c>(
        &self,
        value: String,
        current_block: &'a Block<'c>,
    ) -> Result<OperationRef<'c, 'a>> where 'ctx: 'a, 'ctx: 'c {
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

    fn gen_assignment<'parent_block, 'context, 'varc, 'this>(
        &self,
        lhs_id: &SSAID,
        rhs_id: &SSAID,
        current_block: usize,
        block_references: &'this HashMap<usize, BlockRef<'context, 'parent_block>>,
        variable_store: &'this HashMap<SSAID, Value<'varc, 'parent_block>>,
    ) -> Result<()> where 'ctx: 'context, 'this: 'context {
        debug!("generating assignment {:?} {:?}", lhs_id, rhs_id);
        let rhs_value = self.gen_variable_load(*rhs_id, block_references, variable_store, current_block)?;
        let lhs_ptr = variable_store.get(lhs_id).unwrap().to_owned();

            let store_op = melior::dialect::memref::store(
                rhs_value,
                lhs_ptr.into(),
                &[],
                melior::ir::Location::unknown(self.context),
            );

            let current_block = block_references.get(&current_block).unwrap();

            current_block.append_operation(store_op);


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
        use crate::analysis::type_evaluation::evaluate_types;

        let ir_program = produce_ir(path.to_str().unwrap())?;
        debug!("testing codegen for IR: {ir_program} \n cfg: {:?}", ir_program.control_flow_graphs);
        let ir_types = evaluate_types(&ir_program)?;
        let mlir_generation_config = MlirGenerationConfig {
            verify_mlir: true,
            program: ir_program.clone(),
            program_types: ir_types,
        };


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
