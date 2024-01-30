use std::{cell::RefCell, collections::HashMap, ops::Index};

use anyhow::{bail, Result};
use melior::{
    dialect::{
        func::{self, call},
        llvm::{self, attributes::Linkage, AllocaOptions, LoadStoreOptions},
        DialectRegistry,
    },
    ir::{
        attribute::{
            ArrayAttribute, DenseI32ArrayAttribute, FlatSymbolRefAttribute, IntegerAttribute,
            StringAttribute, TypeAttribute,
        },
        operation::{OperationBuilder, OperationResult},
        r#type::{FunctionType, IntegerType},
        Attribute, AttributeLike, Block, BlockRef, Identifier, Location, Module, Operation,
        OperationRef, Region, Type, Value,
    },
    pass,
    utility::{register_all_dialects, register_all_llvm_translations, register_all_passes},
    Context, ExecutionEngine,
};

use crate::{
    parser::{Ast, FunctionKeyword, TSExpression, TSIdentifier, TSValue},
    typed_ast::{self, Decl, FunctionArg, TypedAst, TypedExpression, TypedProgram},
};

// TODO: something inside the module is dropped when it is returned.
// That is why we return the exection engine at the moment.

/// Creates a `llvm.getelementptr` operation.
pub fn get_element_ptr_typed<'c>(
    context: &'c Context,
    ptr: Value<'c, '_>,
    indices: DenseI32ArrayAttribute<'c>,
    result_type: Type<'c>,
    location: Location<'c>,
) -> Operation<'c> {
    OperationBuilder::new("llvm.getelementptr", location)
        .add_attributes(&[(
            Identifier::new(context, "rawConstantIndices"),
            indices.into(),
        )])
        .add_operands(&[ptr])
        .add_results(&[result_type])
        .build()
}

struct CodeGen<'ctx> {
    context: &'ctx Context,
    annon_string_counter: RefCell<usize>,
    llvm_type_store: HashMap<TSIdentifier, Type<'ctx>>,
    type_store: HashMap<TSIdentifier, typed_ast::Type>,
    var_to_type: HashMap<TSIdentifier, typed_ast::Type>,
}

impl<'ctx> CodeGen<'ctx> {
    fn new(
        context: &'ctx Context,
        types: HashMap<TSIdentifier, typed_ast::Type>,
        variable_types: HashMap<TSIdentifier, typed_ast::Type>,
    ) -> Self {
        Self {
            context,
            annon_string_counter: 0.into(),
            llvm_type_store: HashMap::new(),
            type_store: types,
            var_to_type: variable_types,
        }
    }

    fn gen_annon_string_id(&self) -> String {
        let id = format!("annonstr{}", self.annon_string_counter.borrow());

        self.annon_string_counter
            .replace_with(|&mut v| v + 1 as usize);

        id
    }

    fn gen_declaration<'a>(
        &'a self,
        decl: Decl,
        location: Location<'a>,
        module: &mut Module<'a>,
    ) -> Result<Operation> {
        match decl {
            e @ Decl::Function { .. } => self.gen_function(e, location, module),
            _ => todo!("struct decl"),
        }
    }

    fn gen_function<'a>(
        &'a self,
        decl: Decl,
        location: Location<'a>,
        module: &mut Module<'a>,
    ) -> Result<Operation> {
        let Decl::Function {
            keywords,
            id,
            arguments,
            body,
            return_type,
        } = decl
        else {
            panic!("recived a non function declaration");
        };

        let function_region = Region::new();

        let mut function_block = Block::new(
            arguments
                .iter()
                .map(|_| (llvm::r#type::opaque_pointer(&self.context), location))
                .collect::<Vec<(Type, Location)>>()
                .as_slice(),
        );

        let mut variable_store: HashMap<TSIdentifier, OperationResult> = HashMap::new();
        for exp in body.unwrap_or(vec![]) {
            match exp.clone() {
                TypedAst::Expression(TypedExpression::Call(id, args)) => {
                    // let mut exp_block = function_block;
                    let actual_args: Vec<Value> = args
                        .iter()
                        .map(|arg| match arg {
                            TypedExpression::Value(TSValue::String(ref val), Type) => {
                                // TODO: \n is getting escaped, perhap we need a raw string?
                                let val = if val == "\\n" { "\n" } else { val };

                                let ptr_op = self
                                    .gen_pointer_to_annon_str(
                                        location.clone(),
                                        val.to_string(),
                                        &module,
                                    )
                                    .unwrap();

                                function_block
                                    .append_operation(ptr_op)
                                    .result(0)
                                    .unwrap()
                                    .into()
                            }
                            TypedExpression::Value(TSValue::Variable(ref id), Type) => {
                                if let Some(v) = variable_store.get(id) {
                                    v.to_owned().into()
                                } else {
                                    function_block
                                        .argument(
                                            arguments
                                                .iter()
                                                .position(|farg| &farg.name == id)
                                                .ok_or(format!(
                                                    "failed to match argument: {:?} {id:?} {:?}",
                                                    arguments
                                                        .iter()
                                                        .map(|farg| farg.name.clone())
                                                        .collect::<Vec<TSIdentifier>>(),
                                                    variable_store
                                                ))
                                                .unwrap(),
                                        )
                                        .unwrap()
                                        .into()
                                }
                            }
                            e @ TypedExpression::StructFieldRef(_, _) => self
                                .gen_struct_expression_block(
                                    e.clone(),
                                    location,
                                    &module,
                                    variable_store.clone(),
                                    &function_block,
                                )
                                .unwrap()
                                .unwrap()
                                .into(),
                            TypedExpression::Value(TSValue::Integer(v), _) => {
                                // next
                                let const_op = melior::dialect::arith::constant(
                                    &self.context,
                                    IntegerAttribute::new(
                                        *v as i64,
                                        IntegerType::new(&self.context, 32).into(),
                                    )
                                    .into(),
                                    location,
                                );

                                function_block
                                    .append_operation(const_op)
                                    .result(0)
                                    .unwrap()
                                    .into()
                            }
                            e => todo!("not yet implemented: {:?}", e),
                        })
                        .collect();

                    let fn_type = self.type_store.get(&id).unwrap();

                    let (callee_keywords, return_type) =
                        if let typed_ast::Type::Function(keywords, _, return_type) = fn_type {
                            (keywords, return_type)
                        } else {
                            panic!(
                                "failed to find a function dcelaration or return type for {}",
                                id.0
                            );
                        };

                    if callee_keywords.contains(&FunctionKeyword::LlvmExtern) {
                        let op = OperationBuilder::new("llvm.call", location)
                            .add_operands(&actual_args)
                            .add_attributes(&[(
                                Identifier::new(&self.context, "callee"),
                                FlatSymbolRefAttribute::new(&self.context, &id.0).into(),
                            )]);

                        function_block.append_operation(match **return_type {
                            typed_ast::Type::Unit => op.build(),
                            _ => op
                                .add_results(&[return_type.as_mlir_type(&self.context)])
                                .build(),
                        });
                    } else {
                        let res = function_block.append_operation(func::call(
                            &self.context,
                            FlatSymbolRefAttribute::new(&self.context, &id.0),
                            &actual_args,
                            &[],
                            location,
                        ));
                    }

                    // let call = llvm::ca(
                    //     &self.context,
                    //     FlatSymbolRefAttribute::new(&self.context, "printf"),
                    //     &[op.result(0).unwrap().into()],
                    //     &[Type::none(&self.context)],
                    //     location,
                    // );

                    // block.append_operation(func::r#return(&[], location));
                }
                TypedAst::Expression(TypedExpression::Struct(id, fields)) => {
                    let size = melior::dialect::arith::constant(
                        &self.context,
                        IntegerAttribute::new(
                            4, // TODO why do we need 4 here?
                            IntegerType::new(&self.context, 32).into(),
                        )
                        .into(),
                        location,
                    );
                    let res = function_block.append_operation(size);
                    let ptr_type = if let Some(ty) = self.type_store.get(&id).cloned() {
                        llvm::r#type::pointer(ty.as_mlir_type(self.context), 0)
                    } else {
                        bail!("Could not find a type for ID: {id:?}")
                    };

                    let empty_struct = llvm::alloca(
                        &self.context,
                        res.result(0).unwrap().into(),
                        ptr_type,
                        location,
                        AllocaOptions::new(),
                    );

                    let struct_ptr = function_block.append_operation(empty_struct).result(0)?;

                    let string_type =
                        llvm::r#type::array(IntegerType::new(&self.context, 8).into(), 2 as u32);

                    let string_ptr = llvm::r#type::pointer(string_type, 0);

                    let ele_type = llvm::r#type::r#struct(
                        self.context,
                        &[string_type.clone(), string_type],
                        false,
                    );

                    for (i, f) in fields.into_iter().enumerate() {
                        let field_ptr_op = llvm::get_element_ptr(
                            &self.context,
                            struct_ptr.into(),
                            DenseI32ArrayAttribute::new(&self.context, &[0, i as i32]),
                            ele_type,
                            llvm::r#type::opaque_pointer(&self.context),
                            location,
                        );

                        let field_ptr = function_block.append_operation(field_ptr_op).result(0)?;

                        let exp_ptr_op = self.gen_expression_code(f, location, &module)?;

                        let exp_ptr = function_block.append_operation(exp_ptr_op).result(0)?;

                        let store_op = llvm::store(
                            &self.context,
                            exp_ptr.into(),
                            field_ptr.into(),
                            location,
                            LoadStoreOptions::new(),
                        );

                        function_block.append_operation(store_op);
                    }
                }

                TypedAst::Assignment(id, exp, type_anno) => {
                    // if let TypedExpression::Struct(type_id, _) = exp.clone() {
                    //     self.var_to_type.insert(id.clone(), type_id);
                    // }

                    let exp_op = self.gen_struct_expression_block(
                        exp,
                        location,
                        &module,
                        variable_store.clone(),
                        &function_block,
                    )?;

                    if let Some(exp_op) = exp_op {
                        variable_store.insert(id, exp_op);
                    }
                }

                e => todo!("not yet ready for {:?}", e),
            }
        }

        function_block.append_operation(llvm::r#return(None, location));

        let mut function_block = function_region.append_block(function_block);
        let functiom_decl = if &id.0 == "main" {
            func::func(
                &self.context,
                StringAttribute::new(&self.context, &id.0),
                TypeAttribute::new(
                    FunctionType::new(
                        &self.context,
                        arguments
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
        } else if keywords.contains(&FunctionKeyword::LlvmExtern) {
            llvm::func(
                &self.context,
                StringAttribute::new(&self.context, &id.0),
                TypeAttribute::new(
                    llvm::r#type::function(
                        return_type.as_mlir_type(&self.context),
                        arguments
                            .iter()
                            .map(|a| a.r#type.as_mlir_type(&self.context))
                            .collect::<Vec<Type>>()
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
                StringAttribute::new(&self.context, &id.0),
                TypeAttribute::new(
                    FunctionType::new(
                        &self.context,
                        arguments
                            .iter()
                            .map(|_| llvm::r#type::opaque_pointer(&self.context).into())
                            .collect::<Vec<Type>>()
                            .as_slice(),
                        &[],
                    )
                    .into(),
                ),
                function_region,
                &[],
                location,
            )
        };

        Ok(functiom_decl)
    }

    fn gen_ast_code(&self, ast: TypedProgram, emit_mlir: bool) -> Result<Module> {
        let location = Location::unknown(&self.context);
        let mut module = Module::new(location);

        for node in ast.ast {
            let mut variable_store: HashMap<TSIdentifier, OperationResult> = HashMap::new();
            match node.clone() {
                TypedAst::Decl(
                    ref d @ Decl::Function {
                        ref id,
                        ref arguments,
                        ref body,
                        ref return_type,
                        ..
                    },
                ) => {
                    let function_decl = self.gen_declaration(d.clone(), location, &mut module)?;

                    module.body().append_operation(function_decl);
                }
                TypedAst::Decl(Decl::Struct(..)) => {}
                _ => todo!(),
            }
        }

        Ok(module)
    }

    fn gen_struct_expression_block<'a, 'c>(
        &'a self,
        exp: TypedExpression,
        location: Location<'a>,
        module: &Module,
        llvm_value_store: HashMap<TSIdentifier, OperationResult<'a, 'a>>,
        function_block: &'a Block,
    ) -> Result<Option<OperationResult>>
    where
        'a: 'c,
    {
        let res = match exp {
            TypedExpression::Call(id, args) => {
                // let mut exp_block = function_block;
                let actual_args: Vec<Value> = args
                    .iter()
                    .map(|arg| match arg {
                        TypedExpression::Value(TSValue::String(ref val), Type) => {
                            // TODO: \n is getting escaped, perhap we need a raw string?
                            let val = if val == "\\n" { "\n" } else { val };

                            let ptr_op = self
                                .gen_pointer_to_annon_str(
                                    location.clone(),
                                    val.to_string(),
                                    &module,
                                )
                                .unwrap();

                            function_block
                                .append_operation(ptr_op)
                                .result(0)
                                .unwrap()
                                .into()
                        }
                        TypedExpression::Value(TSValue::Integer(v), _) => {
                            let op = melior::dialect::arith::constant(
                                &self.context,
                                IntegerAttribute::new(
                                    *v as i64, // TODO why do we need 4 here?
                                    IntegerType::new(&self.context, 32).into(),
                                )
                                .into(),
                                location,
                            );
                            function_block
                                .append_operation(op)
                                .result(0)
                                .unwrap()
                                .into()
                        }
                        _ => todo!(),
                    })
                    .collect();

                if let Some(typed_ast::Type::Function(ref keywords, _, ref return_type)) =
                    self.type_store.get(&id)
                {
                    if keywords.contains(&FunctionKeyword::LlvmExtern) {
                        let res = function_block.append_operation(
                            OperationBuilder::new("llvm.call", location)
                                .add_operands(&actual_args)
                                .add_attributes(&[(
                                    Identifier::new(&self.context, "callee"),
                                    FlatSymbolRefAttribute::new(&self.context, &id.0).into(),
                                )])
                                .add_results(&[return_type.as_mlir_type(&self.context).into()])
                                .build(),
                        );

                        match res.result(0) {
                            Ok(res) => return Ok(Some(res)),
                            _ => return Ok(None),
                        }
                    }
                }

                if &id.0 == "printf" {
                    function_block.append_operation(
                        OperationBuilder::new("llvm.call", location)
                            .add_operands(&actual_args)
                            .add_attributes(&[(
                                Identifier::new(&self.context, "callee"),
                                FlatSymbolRefAttribute::new(&self.context, "printf").into(),
                            )])
                            .add_results(&[IntegerType::new(&self.context, 32).into()])
                            .build(),
                    );
                    None
                } else if &id.0 == "fdopen" {
                    Some(
                        function_block
                            .append_operation(
                                OperationBuilder::new("llvm.call", location)
                                    .add_operands(&actual_args)
                                    .add_attributes(&[(
                                        Identifier::new(&self.context, "callee"),
                                        FlatSymbolRefAttribute::new(&self.context, &id.0).into(),
                                    )])
                                    .add_results(&[llvm::r#type::opaque_pointer(&self.context)])
                                    .build(),
                            )
                            .result(0)
                            .unwrap(),
                    )
                } else {
                    Some(
                        function_block
                            .append_operation(func::call(
                                &self.context,
                                FlatSymbolRefAttribute::new(&self.context, &id.0),
                                &actual_args,
                                &[llvm::r#type::opaque_pointer(&self.context)],
                                location,
                            ))
                            .result(0)
                            .unwrap(),
                    )
                }
            }

            // TODO: NEXT remove the need to mutate type stores in codgen.
            TypedExpression::StructFieldRef(struct_id, field_id) => {
                let struct_type = self.var_to_type.get(&struct_id).unwrap();
                let struct_ptr = llvm_value_store.get(&struct_id).unwrap().to_owned();

                let Some(field_index) = (if let typed_ast::Type::Struct(fields) = struct_type {
                    fields.iter().position(|f| f.0 == field_id)
                } else {
                    bail!(
                        "Expected to find a struct type for variable {} instead found {:#?}",
                        struct_id.0,
                        struct_type
                    );
                }) else {
                    bail!(
                        "Failed to find field {} in struct {:?}",
                        field_id.0,
                        struct_type
                    );
                };

                let gep = llvm::get_element_ptr(
                    self.context,
                    struct_ptr.into(),
                    DenseI32ArrayAttribute::new(self.context, &[0, field_index as i32]),
                    struct_type.as_mlir_type(&self.context).to_owned(),
                    llvm::r#type::opaque_pointer(self.context),
                    location,
                );

                let struct_field_ref = function_block.append_operation(gep).result(0).unwrap();

                let v = llvm::load(
                    &self.context,
                    struct_field_ref.into(),
                    llvm::r#type::opaque_pointer(self.context),
                    location,
                    LoadStoreOptions::new(),
                );

                Some(function_block.append_operation(v).result(0).unwrap())
            }
            TypedExpression::Struct(id, fields) => {
                let size = melior::dialect::arith::constant(
                    &self.context,
                    IntegerAttribute::new(1, IntegerType::new(&self.context, 32).into()).into(),
                    location,
                );

                let res = function_block.append_operation(size);
                let ptr_type = if let Some(ty) = self.type_store.get(&id).cloned() {
                    llvm::r#type::pointer(ty.as_mlir_type(self.context), 0)
                } else {
                    bail!("Could not find an LLVM type for ID: {id:?}")
                };

                let str_type = |val: String| {
                    llvm::r#type::array(IntegerType::new(&self.context, 8).into(), val.len() as u32)
                };

                let str_ptr_type = |val: String| llvm::r#type::pointer(str_type(val), 0);

                let exp_ptr = |exp: TypedExpression| match exp {
                    TypedExpression::Value(TSValue::String(val), etype) => str_ptr_type(val),
                    _ => todo!("missing implementation"),
                };

                let struct_type = llvm::r#type::r#struct(
                    self.context,
                    fields
                        .clone()
                        .into_iter()
                        .map(exp_ptr)
                        .collect::<Vec<Type>>()
                        .as_slice(),
                    true,
                );

                let empty_struct = llvm::alloca(
                    &self.context,
                    res.result(0).unwrap().into(),
                    ptr_type,
                    location,
                    AllocaOptions::new(),
                );

                let struct_ptr = function_block.append_operation(empty_struct).result(0)?;

                for (i, f) in fields.into_iter().enumerate() {
                    let field_ptr_op = llvm::get_element_ptr(
                        &self.context,
                        struct_ptr.into(),
                        DenseI32ArrayAttribute::new(&self.context, &[0, i as i32]),
                        struct_type,
                        llvm::r#type::opaque_pointer(&self.context),
                        location,
                    );

                    let field_ptr = function_block.append_operation(field_ptr_op).result(0)?;

                    let exp_ptr_op = self.gen_expression_code(f, location, &module)?;

                    let exp_ptr = function_block.append_operation(exp_ptr_op).result(0)?;

                    let store_op = llvm::store(
                        &self.context,
                        exp_ptr.into(),
                        field_ptr.into(),
                        location,
                        LoadStoreOptions::new(),
                    );

                    function_block.append_operation(store_op);
                }

                Some(struct_ptr)
            }
            e => todo!("unimplemented: {e:?}"),
        };

        Ok(res)
    }

    fn gen_expression_code<'a, 'c>(
        &'a self,
        exp: TypedExpression,
        location: Location<'a>,
        module: &Module,
    ) -> Result<Operation<'c>>
    where
        'a: 'c,
    {
        let res: Operation = match exp {
            TypedExpression::Value(TSValue::String(val), vtype) => {
                // TODO: \n is getting escaped, perhap we need a raw string?
                let val = if val == "\\n" { "\n" } else { &val };

                self.gen_pointer_to_annon_str(location, val.to_string(), &module)?
            }
            TypedExpression::Value(TSValue::Integer(v), _) => {
                melior::dialect::arith::constant(
                    &self.context,
                    IntegerAttribute::new(
                        4, // TODO why do we need 4 here?
                        IntegerType::new(&self.context, 32).into(),
                    )
                    .into(),
                    location,
                )
            }

            _ => todo!(),
        };

        Ok(res)
    }

    pub fn gen_pointer_to_annon_str<'a>(
        &'a self,
        location: Location<'a>,
        value: String,
        module: &Module,
    ) -> Result<Operation<'a>> {
        let string_id = self.generate_annon_string(value, module, location);
        self.gen_pointer_to_global(string_id, location)
    }

    fn generate_annon_string(&self, value: String, module: &Module, location: Location) -> String {
        let id = self.gen_annon_string_id();
        let string_type = llvm::r#type::array(
            IntegerType::new(&self.context, 8).into(),
            (value.len()) as u32,
        );
        let op = OperationBuilder::new("llvm.mlir.global", location)
            .add_regions(vec![Region::new()])
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
                    // ArrayAttribute::new(&self.context, &[]).into(),
                    llvm::attributes::linkage(&self.context, Linkage::Internal),
                ),
            ])
            .build();

        module.body().append_operation(op);

        id
    }

    pub fn gen_pointer_to_global<'a>(
        &'a self,
        id: String,
        location: Location<'a>,
    ) -> Result<Operation<'a>> {
        let address_op = OperationBuilder::new("llvm.mlir.addressof", location)
            // .enable_result_type_inference()
            .add_attributes(&[(
                Identifier::new(&self.context, "global_name"),
                FlatSymbolRefAttribute::new(&self.context, &id).into(),
            )])
            .add_results(&[llvm::r#type::opaque_pointer(&self.context)])
            .build();

        Ok(address_op)
    }
}

pub fn generate_mlir<'c>(ast: TypedProgram, emit_mlir: bool) -> Result<ExecutionEngine> {
    let context = Context::new();
    let registry = DialectRegistry::new();
    register_all_dialects(&registry);
    context.append_dialect_registry(&registry);
    context.get_or_load_dialect("func");
    context.get_or_load_dialect("arith");
    context.get_or_load_dialect("llvm");
    register_all_llvm_translations(&context);
    let code_gen = CodeGen::new(&context, ast.types.clone(), ast.variable_types.clone());

    let mut module = code_gen.gen_ast_code(ast, emit_mlir)?;
    if !emit_mlir {
        assert!(module.as_operation().verify());
    }

    let pass_manager = pass::PassManager::new(&code_gen.context);
    register_all_passes();
    pass_manager.enable_verifier(true);
    pass_manager.add_pass(pass::conversion::create_control_flow_to_llvm());
    pass_manager.add_pass(pass::conversion::create_func_to_llvm());
    // pass_manager.add_pass(pass::conversion::create_index_to_llvm_pass());
    // pass_manager.add_pass(pass::conversion::create_mem_ref_to_llvm());
    pass_manager.add_pass(pass::conversion::create_reconcile_unrealized_casts());
    pass::conversion::register_func_to_llvm();

    // pass_manager.enable_ir_printing();

    pass_manager
        .nested_under("func.func")
        .add_pass(pass::conversion::create_arith_to_llvm());
    pass_manager.run(&mut module);

    if emit_mlir {
        println!("{}", module.as_operation());
    }

    let engine = ExecutionEngine::new(&module, 0, &[], true);

    Ok(engine)

    // for node in ast.0 {
    //     match node {
    //         TypedAst::Function(id, fargs, body) => {
    //             let region = Region::new();
    //             let function_block = Block::new(
    //                 fargs
    //                     .iter()
    //                     .map(|_| (llvm::r#type::opaque_pointer(&context), location))
    //                     .collect::<Vec<(Type, Location)>>()
    //                     .as_slice(),
    //             );

    //             let function_block = region.append_block(function_block);

    //             for exp in body {
    //                 match exp.clone() {
    //                     TypedAst::Expression(TSExpression::Call(id, args)) => {
    //                         let exp_block = function_block;
    //                         let actual_args: Vec<Value> = args
    //                             .iter()
    //                             .map(|arg| match arg {
    //                                 TSExpression::Value(TSValue::String(ref val)) => {
    //                                     // TODO: \n is getting escaped, perhap we need a raw string?
    //                                     let val = if val == "\\n" { "\n" } else { val };

    //                                     gen_pointer_to_annon_str(
    //                                         &context,
    //                                         &mut gen_annon_string,
    //                                         &exp_block,
    //                                         location.clone(),
    //                                         val.to_string(),
    //                                         &mut module,
    //                                     )
    //                                     .unwrap()
    //                                     .into()
    //                                 }
    //                                 TSExpression::Value(TSValue::Variable(ref id)) => exp_block
    //                                     .argument(
    //                                         fargs
    //                                             .iter()
    //                                             .position(|farg| &farg.0 == id)
    //                                             .ok_or(format!(
    //                                                 "failed to match argument: {:?} {id}",
    //                                                 fargs
    //                                                     .iter()
    //                                                     .map(|farg| farg.clone())
    //                                                     .collect::<Vec<TSIdentifier>>()
    //                                             ))
    //                                             .unwrap(),
    //                                     )
    //                                     .unwrap()
    //                                     .into(),
    //                                 _ => todo!(),
    //                             })
    //                             .collect();

    //                         let res = exp_block.append_operation(
    //                             OperationBuilder::new("llvm.call", location)
    //                                 .add_operands(&actual_args)
    //                                 .add_attributes(&[(
    //                                     Identifier::new(&context, "callee"),
    //                                     FlatSymbolRefAttribute::new(&context, "printf").into(),
    //                                 )])
    //                                 .add_results(&[IntegerType::new(&context, 32).into()])
    //                                 .build(),
    //                         );

    //                         // let call = llvm::ca(
    //                         //     &context,
    //                         //     FlatSymbolRefAttribute::new(&context, "printf"),
    //                         //     &[op.result(0).unwrap().into()],
    //                         //     &[Type::none(&context)],
    //                         //     location,
    //                         // );

    //                         // block.append_operation(func::r#return(&[], location));
    //                     }
    //                     TypedAst::Expression(TSExpression::Struct(id, fields)) => {
    //                         let size = melior::dialect::arith::constant(
    //                             &context,
    //                             IntegerAttribute::new(0, IntegerType::new(&context, 0).into())
    //                                 .into(),
    //                             location,
    //                         );
    //                         let res = function_block.append_operation(size);
    //                         let ptr_type = llvm::r#type::pointer(*llvm_types.get(&id).unwrap(), 0);
    //                         let empty_struct = llvm::alloca(
    //                             &context,
    //                             res.result(0).unwrap().into(),
    //                             ptr_type,
    //                             location,
    //                             AllocaOptions::new(),
    //                         );

    //                         let struct_ptr =
    //                             function_block.append_operation(empty_struct).result(0)?;

    //                         for (i, f) in fields.into_iter().enumerate() {
    //                             let field_ptr_op = llvm::get_element_ptr(
    //                                 &context,
    //                                 struct_ptr.into(),
    //                                 DenseI32ArrayAttribute::new(&context, &[0, i as i32]),
    //                                 llvm::r#type::opaque_pointer(&context),
    //                                 llvm::r#type::opaque_pointer(&context),
    //                                 location,
    //                             );

    //                             let field_ptr =
    //                                 function_block.append_operation(field_ptr_op).result(0)?;
    //                         }
    //                     }
    //                     e => todo!("not yet ready for {:?}", e),
    //                 }
    //             }
    //             function_block.append_operation(llvm::r#return(None, location));

    //             let function = func::func(
    //                 &context,
    //                 StringAttribute::new(&context, &id.0),
    //                 TypeAttribute::new(
    //                     FunctionType::new(
    //                         &context,
    //                         fargs
    //                             .iter()
    //                             .map(|_| llvm::r#type::opaque_pointer(&context).into())
    //                             .collect::<Vec<Type>>()
    //                             .as_slice(),
    //                         &[],
    //                     )
    //                     .into(),
    //                 ),
    //                 region,
    //                 &[(
    //                     Identifier::new(&context, "llvm.emit_c_interface"),
    //                     Attribute::unit(&context),
    //                 )],
    //                 location,
    //             );

    //             module.body().append_operation(function);
    //         }
    //         TypedAst::StructType(id, fields) => {
    //             let struct_ty = llvm::r#type::r#struct(
    //                 &context,
    //                 fields
    //                     .into_iter()
    //                     .map(|f| llvm::r#type::opaque_pointer(&context))
    //                     .collect::<Vec<Type>>()
    //                     .as_slice(),
    //                 true,
    //             );

    //             llvm_types.insert(id, struct_ty);
    //         }
    //         _ => todo!(),
    //     }
    // }

    // assert!(module.as_operation().verify());

    // let pass_manager = pass::PassManager::new(&code_gen.context);
    // register_all_passes();
    // pass_manager.enable_verifier(true);
    // pass_manager.add_pass(pass::conversion::create_control_flow_to_llvm());
    // pass_manager.add_pass(pass::conversion::create_func_to_llvm());
    // pass_manager.add_pass(pass::conversion::create_index_to_llvm_pass());
    // pass_manager.add_pass(pass::conversion::create_mem_ref_to_llvm());
    // pass_manager.add_pass(pass::conversion::create_reconcile_unrealized_casts());

    // // pass_manager.enable_ir_printing();

    // pass_manager
    //     .nested_under("func.func")
    //     .add_pass(pass::conversion::create_arith_to_llvm());
    // pass_manager.run(&mut module).unwrap();

    // if emit_mlir {
    //     println!("{}", module.as_operation());
    // }

    // let engine = ExecutionEngine::new(&module, 0, &[], true);

    // Ok(engine)
}
