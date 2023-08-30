use std::ops::Index;

use anyhow::Result;
use melior::{
    dialect::{
        func,
        llvm::{self, attributes::Linkage},
        DialectRegistry,
    },
    ir::{
        attribute::{FlatSymbolRefAttribute, StringAttribute, TypeAttribute},
        operation::{OperationBuilder, OperationResult},
        r#type::{FunctionType, IntegerType},
        Attribute, Block, Identifier, Location, Module, Region, Type, Value,
    },
    pass,
    utility::{register_all_dialects, register_all_llvm_translations, register_all_passes},
    Context, ExecutionEngine,
};

use crate::parser::{Ast, TSExpression, TSIdentifier, TSValue, TypedAst};

// TODO: something inside the module is dropped when it is returned.
// That is why we return the exection engine at the moment.

pub fn generate_mlir<'c>(ast: Ast, emit_mlir: bool) -> Result<ExecutionEngine> {
    let registry = DialectRegistry::new();
    register_all_dialects(&registry);
    let context = Context::new();
    context.append_dialect_registry(&registry);
    context.get_or_load_dialect("func");
    context.get_or_load_dialect("arith");
    context.get_or_load_dialect("llvm");
    register_all_llvm_translations(&context);

    let location = Location::unknown(&context);
    let mut module = Module::new(location);
    let location = Location::unknown(&context);
    let mut module = Module::new(location);

    let mut annon_string_counter = 1;
    let integer_type = IntegerType::new(&context, 64);

    let mut gen_annon_string = || {
        let id = format!("annonstr{annon_string_counter}");
        annon_string_counter += 1;
        id
    };

    for node in ast.0 {
        match node {
            TypedAst::Function(id, fargs, body) => {
                let region = Region::new();
                let function_block = Block::new(
                    fargs
                        .iter()
                        .map(|_| (llvm::r#type::opaque_pointer(&context), location))
                        .collect::<Vec<(Type, Location)>>()
                        .as_slice(),
                );

                let function_block = region.append_block(function_block);

                for exp in body {
                    match exp.clone() {
                        TypedAst::Expression(TSExpression::Call(id, args)) => {
                            let exp_block = function_block;
                            let actual_args: Vec<Value> = args
                                .iter()
                                .map(|arg| match arg {
                                    TSExpression::Value(TSValue::String(ref val)) => {
                                        // TODO: \n is getting escaped, perhap we need a raw string?
                                        let val = if val == "\\n" { "\n" } else { val };

                                        gen_pointer_to_annon_str(
                                            &context,
                                            &mut gen_annon_string,
                                            &exp_block,
                                            location.clone(),
                                            val.to_string(),
                                            &mut module,
                                        )
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
                                        Identifier::new(&context, "callee"),
                                        FlatSymbolRefAttribute::new(&context, "printf").into(),
                                    )])
                                    .add_results(&[IntegerType::new(&context, 32).into()])
                                    .build(),
                            );

                            // let call = llvm::ca(
                            //     &context,
                            //     FlatSymbolRefAttribute::new(&context, "printf"),
                            //     &[op.result(0).unwrap().into()],
                            //     &[Type::none(&context)],
                            //     location,
                            // );

                            // block.append_operation(func::r#return(&[], location));
                        }
                        _ => todo!(),
                    }
                }
                function_block.append_operation(llvm::r#return(None, location));

                let function = func::func(
                    &context,
                    StringAttribute::new(&context, &id.0),
                    TypeAttribute::new(
                        FunctionType::new(
                            &context,
                            fargs
                                .iter()
                                .map(|_| llvm::r#type::opaque_pointer(&context).into())
                                .collect::<Vec<Type>>()
                                .as_slice(),
                            &[],
                        )
                        .into(),
                    ),
                    region,
                    &[(
                        Identifier::new(&context, "llvm.emit_c_interface"),
                        Attribute::unit(&context),
                    )],
                    location,
                );

                module.body().append_operation(function);
            }
            _ => todo!(),
        }
    }

    let printf_decl = llvm::func(
        &context,
        StringAttribute::new(&context, "printf"),
        TypeAttribute::new(
            llvm::r#type::function(
                IntegerType::new(&context, 32).into(),
                &[llvm::r#type::opaque_pointer(&context)],
                true,
            )
            .into(),
        ),
        Region::new(),
        &[
            (
                Identifier::new(&context, "sym_visibility"),
                StringAttribute::new(&context, "private").into(),
            ),
            (
                Identifier::new(&context, "llvm.emit_c_interface"),
                Attribute::unit(&context),
            ),
        ],
        location,
    );

    module.body().append_operation(printf_decl);

    assert!(module.as_operation().verify());

    let pass_manager = pass::PassManager::new(&context);
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
}

pub fn gen_pointer_to_annon_str<'c, 'a>(
    context: &'c Context,
    id_generator: &mut impl FnMut() -> String,
    block: &'c Block<'c>,
    location: Location<'c>,
    value: String,
    module: &mut Module,
) -> Result<OperationResult<'c, 'a>>
where
    'c: 'a,
{
    let string_id = generate_annon_string(id_generator, value, module, location, context);
    gen_pointer_to_global(&context, string_id, block, location)
}

pub fn generate_annon_string(
    id_generator: &mut impl FnMut() -> String,
    value: String,
    module: &mut Module,
    location: Location,
    context: &Context,
) -> String {
    let id = id_generator();
    let string_type = llvm::r#type::array(IntegerType::new(&context, 8).into(), value.len() as u32);
    let op = OperationBuilder::new("llvm.mlir.global", location)
        .add_regions(vec![Region::new()])
        .add_attributes(&[
            (
                Identifier::new(&context, "value"),
                StringAttribute::new(&context, &value).into(),
            ),
            (
                Identifier::new(&context, "sym_name"),
                StringAttribute::new(&context, &id).into(),
            ),
            (
                Identifier::new(&context, "global_type"),
                TypeAttribute::new(string_type).into(),
            ),
            (
                Identifier::new(&context, "linkage"),
                // ArrayAttribute::new(&context, &[]).into(),
                llvm::attributes::linkage(&context, Linkage::Internal),
            ),
        ])
        .build();

    module.body().append_operation(op);

    id
}

pub fn gen_pointer_to_global<'c, 'a>(
    context: &'c Context,
    id: String,
    block: &'c Block<'c>,
    location: Location<'c>,
) -> Result<OperationResult<'c, 'a>>
where
    'c: 'a,
{
    let address_op = OperationBuilder::new("llvm.mlir.addressof", location)
        // .enable_result_type_inference()
        .add_attributes(&[(
            Identifier::new(&context, "global_name"),
            FlatSymbolRefAttribute::new(&context, &id).into(),
        )])
        .add_results(&[llvm::r#type::opaque_pointer(&context)])
        .build();

    Ok(block.append_operation(address_op).result(0)?)
}
