use std::{cell::RefCell, collections::HashMap, ops::Index};

use anyhow::{bail, Result};
use melior::{
    dialect::{
        func,
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
        Attribute, Block, Identifier, Location, Module, Operation, Region, Type, Value,
    },
    pass,
    utility::{register_all_dialects, register_all_llvm_translations, register_all_passes},
    Context, ExecutionEngine,
};

use crate::parser::{Ast, TSExpression, TSIdentifier, TSValue, TypedAst};

// TODO: something inside the module is dropped when it is returned.
// That is why we return the exection engine at the moment.

struct CodeGen {
    context: Context,
    annon_string_counter: RefCell<usize>,
}

impl CodeGen {
    fn new() -> Self {
        let registry = DialectRegistry::new();
        register_all_dialects(&registry);
        let context = Context::new();
        context.append_dialect_registry(&registry);
        context.get_or_load_dialect("func");
        context.get_or_load_dialect("arith");
        context.get_or_load_dialect("llvm");
        register_all_llvm_translations(&context);

        Self {
            context: context,
            annon_string_counter: 0.into(),
        }
    }

    fn gen_annon_string_id(&self) -> String {
        let id = format!("annonstr{}", self.annon_string_counter.borrow());

        self.annon_string_counter
            .replace_with(|&mut v| v + 1 as usize);

        id
    }

    fn gen_ast_code(&self, ast: Ast, emit_mlir: bool) -> Result<Module> {
        let location = Location::unknown(&self.context);
        let mut llvm_type_store: HashMap<TSIdentifier, Type<'_>> = HashMap::new();

        let mut module = Module::new(location);

        let printf_decl = llvm::func(
            &self.context,
            StringAttribute::new(&self.context, "printf"),
            TypeAttribute::new(
                llvm::r#type::function(
                    IntegerType::new(&self.context, 32).into(),
                    &[llvm::r#type::opaque_pointer(&self.context)],
                    true,
                )
                .into(),
            ),
            Region::new(),
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
        );

        module.body().append_operation(printf_decl);

        for node in ast.0 {
            match node {
                TypedAst::Function(id, fargs, body) => {
                    let region = Region::new();
                    let function_block = Block::new(
                        fargs
                            .iter()
                            .map(|_| (llvm::r#type::opaque_pointer(&self.context), location))
                            .collect::<Vec<(Type, Location)>>()
                            .as_slice(),
                    );

                    let mut function_block = region.append_block(function_block);

                    for exp in body {
                        match exp.clone() {
                            TypedAst::Expression(TSExpression::Call(id, args)) => {
                                let mut exp_block = function_block;
                                let actual_args: Vec<Value> = args
                                    .iter()
                                    .map(|arg| match arg {
                                        TSExpression::Value(TSValue::String(ref val)) => {
                                            // TODO: \n is getting escaped, perhap we need a raw string?
                                            let val = if val == "\\n" { "\n" } else { val };

                                            let ptr_op = self
                                                .gen_pointer_to_annon_str(
                                                    location.clone(),
                                                    val.to_string(),
                                                    &module,
                                                )
                                                .unwrap();

                                            exp_block
                                                .append_operation(ptr_op)
                                                .result(0)
                                                .unwrap()
                                                .into()
                                        }
                                        TSExpression::Value(TSValue::Variable(ref id)) => exp_block
                                            .argument(
                                                fargs
                                                    .iter()
                                                    .position(|farg| &farg.0 == id)
                                                    .ok_or(format!(
                                                        "failed to match argument: {:?} {id}",
                                                        fargs
                                                            .iter()
                                                            .map(|farg| farg.clone())
                                                            .collect::<Vec<TSIdentifier>>()
                                                    ))
                                                    .unwrap(),
                                            )
                                            .unwrap()
                                            .into(),
                                        _ => todo!(),
                                    })
                                    .collect();

                                let res = exp_block.append_operation(
                                    OperationBuilder::new("llvm.call", location)
                                        .add_operands(&actual_args)
                                        .add_attributes(&[(
                                            Identifier::new(&self.context, "callee"),
                                            FlatSymbolRefAttribute::new(&self.context, "printf")
                                                .into(),
                                        )])
                                        .add_results(&[IntegerType::new(&self.context, 32).into()])
                                        .build(),
                                );

                                // let call = llvm::ca(
                                //     &self.context,
                                //     FlatSymbolRefAttribute::new(&self.context, "printf"),
                                //     &[op.result(0).unwrap().into()],
                                //     &[Type::none(&self.context)],
                                //     location,
                                // );

                                // block.append_operation(func::r#return(&[], location));
                            }
                            TypedAst::Expression(TSExpression::Struct(id, fields)) => {
                                let size = melior::dialect::arith::constant(
                                    &self.context,
                                    IntegerAttribute::new(
                                        0,
                                        IntegerType::new(&self.context, 0).into(),
                                    )
                                    .into(),
                                    location,
                                );
                                let res = function_block.append_operation(size);
                                let ptr_type = if let Some(&ty) = llvm_type_store.get(&id) {
                                    llvm::r#type::pointer(ty, 0)
                                } else {
                                    bail!("Could not find an LLVM type for ID: {id:?}")
                                };

                                let empty_struct = llvm::alloca(
                                    &self.context,
                                    res.result(0).unwrap().into(),
                                    ptr_type,
                                    location,
                                    AllocaOptions::new(),
                                );

                                let struct_ptr =
                                    function_block.append_operation(empty_struct).result(0)?;

                                for (i, f) in fields.into_iter().enumerate() {
                                    let field_ptr_op = llvm::get_element_ptr(
                                        &self.context,
                                        struct_ptr.into(),
                                        DenseI32ArrayAttribute::new(&self.context, &[i as i32]),
                                        llvm::r#type::opaque_pointer(&self.context),
                                        llvm::r#type::opaque_pointer(&self.context),
                                        location,
                                    );

                                    let field_ptr =
                                        function_block.append_operation(field_ptr_op).result(0)?;

                                    let exp_ptr_op =
                                        self.gen_expression_code(f, location, &module)?;

                                    let exp_ptr =
                                        function_block.append_operation(exp_ptr_op).result(0)?;

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
                            e => todo!("not yet ready for {:?}", e),
                        }
                    }
                    function_block.append_operation(llvm::r#return(None, location));

                    let function = func::func(
                        &self.context,
                        StringAttribute::new(&self.context, &id.0),
                        TypeAttribute::new(
                            FunctionType::new(
                                &self.context,
                                fargs
                                    .iter()
                                    .map(|_| llvm::r#type::opaque_pointer(&self.context).into())
                                    .collect::<Vec<Type>>()
                                    .as_slice(),
                                &[],
                            )
                            .into(),
                        ),
                        region,
                        &[(
                            Identifier::new(&self.context, "llvm.emit_c_interface"),
                            Attribute::unit(&self.context),
                        )],
                        location,
                    );

                    module.body().append_operation(function);
                }
                TypedAst::StructType(id, fields) => {
                    let struct_ty = llvm::r#type::r#struct(
                        &self.context,
                        fields
                            .into_iter()
                            .map(|f| llvm::r#type::opaque_pointer(&self.context))
                            .collect::<Vec<Type>>()
                            .as_slice(),
                        true,
                    );

                    llvm_type_store.insert(id, struct_ty);
                }
                _ => todo!(),
            }
        }

        Ok(module)
    }

    fn gen_expression_code<'a>(
        &'a self,
        exp: TSExpression,
        location: Location<'a>,
        module: &Module,
    ) -> Result<Operation> {
        let res: Operation = match exp {
            TSExpression::Value(TSValue::String(val)) => {
                // TODO: \n is getting escaped, perhap we need a raw string?
                let val = if val == "\\n" { "\n" } else { &val };

                self.gen_pointer_to_annon_str(location, val.to_string(), &module)?
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
            value.len() as u32,
        );
        let op = OperationBuilder::new("llvm.mlir.global", location)
            .add_regions(vec![Region::new()])
            .add_attributes(&[
                (
                    Identifier::new(&self.context, "value"),
                    StringAttribute::new(&self.context, &value).into(),
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

pub fn generate_mlir<'c>(ast: Ast, emit_mlir: bool) -> Result<ExecutionEngine> {
    let code_gen = CodeGen::new();

    let mut module = code_gen.gen_ast_code(ast, emit_mlir)?;
    assert!(module.as_operation().verify());

    let pass_manager = pass::PassManager::new(&code_gen.context);
    register_all_passes();
    pass_manager.enable_verifier(true);
    pass_manager.add_pass(pass::conversion::create_control_flow_to_llvm());
    pass_manager.add_pass(pass::conversion::create_func_to_llvm());
    pass_manager.add_pass(pass::conversion::create_index_to_llvm_pass());
    pass_manager.add_pass(pass::conversion::create_mem_ref_to_llvm());
    pass_manager.add_pass(pass::conversion::create_reconcile_unrealized_casts());

    // pass_manager.enable_ir_printing();

    pass_manager
        .nested_under("func.func")
        .add_pass(pass::conversion::create_arith_to_llvm());
    pass_manager.run(&mut module).unwrap();

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
