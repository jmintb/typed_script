use std::{iter::FlatMap, sync::mpsc::TrySendError};

use mlir_sys::mlirLLVMArrayTypeGet;
use pest::{iterators::Pair, Parser};
use pest_derive::{self, Parser};

use melior::{
    dialect::{
        self, arith, func,
        llvm::{self, r#type::void},
        DialectRegistry,
    },
    ir::{
        attribute::{ArrayAttribute, FlatSymbolRefAttribute, StringAttribute, TypeAttribute},
        operation::OperationBuilder,
        r#type::{FunctionType, IntegerType, MemRefType},
        Location, *,
    },
    pass::{
        self,
        conversion::{create_arith_to_llvm, create_func_to_llvm},
        Pass, PassManager,
    },
    utility::{register_all_dialects, register_all_llvm_translations, register_all_passes},
    Context, ExecutionEngine,
};

#[derive(Parser)]
#[grammar = "typed_script.pest"]
struct TSParser;

#[derive(Debug)]
pub enum TSExpression {
    Value(TSValue),
    Call(TSIdentifier, Vec<TSExpression>),
}

#[derive(Debug)]
pub enum TSValue {
    String(String),
    Variable(String),
    Number,
    Boolean,
}

#[derive(Debug)]
pub enum TSType {
    String,
    Number,
    Boolean,
    Function,
}

#[derive(Debug)]
pub struct TSIdentifier(String);

#[derive(Debug)]
pub enum TypedAst {
    Value(TSValue, TSType),
    Expression(TSExpression),
    Assignment(TSIdentifier, TSExpression),
    Function(TSIdentifier, Vec<TypedAst>),
}

fn main() {
    let parsed_res = TSParser::parse(
        Rule::program,
        "fn main () { 
            printf(\"hello\");
         }",
    )
    .unwrap();

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

    let mut ast: Vec<TypedAst> = vec![];

    let statements = parsed_res.into_iter();

    for rule in statements {
        println!("statement: {:?}", rule.as_rule());
        let node = match rule.as_rule() {
            Rule::program => todo!(),
            Rule::expression => TypedAst::Expression(parse_expression(rule).unwrap()),
            Rule::assignment => parse_assignment(rule).unwrap(),
            Rule::function => {
                let mut inner = rule.into_inner();

                let identifer = TSIdentifier(inner.next().unwrap().as_str().to_string());

                let body = inner
                    .map(|exp| TypedAst::Expression(parse_expression(exp).unwrap()))
                    .collect();

                TypedAst::Function(identifer, body)
            }
            Rule::EOI => break,
            _ => panic!("unexpected rule {:?}", rule.as_rule()),
        };

        ast.push(node);
    }

    println!("ast: {:?}", ast);

    for node in ast.iter() {
        match node {
            TypedAst::Function(id, body) => for node in ast.iter() {},
            _ => (),
        }
    }

    let integer_type = IntegerType::new(&context, 64);

    for node in ast {
        if let TypedAst::Function(id, body) = node {
            let region = Region::new();
            let block = Block::new(&[]);

            for exp in body {
                match exp {
                    TypedAst::Expression(TSExpression::Call(id, args)) => {
                        let TSExpression::Value(TSValue::String(ref val)) =
                            args[0] else {todo!()};

                        let arr_type =
                            llvm::r#type::array(IntegerType::new(&context, 32).into(), 2 as u32);
                        let op = OperationBuilder::new("somestir", location)
                            .add_attributes(&[(
                                Identifier::new(&context, "value"),
                                // ArrayAttribute::new(&context, &[]).into(),
                                StringAttribute::new(&context, &"dl").into(),
                            )])
                            .enable_result_type_inference()
                            .build();

                        func::call(
                            &context,
                            FlatSymbolRefAttribute::new(&context, "printf"),
                            &[op.result(0).unwrap().into()],
                            &[Type::none(&context)],
                            location,
                        );

                        block.append_operation(op);
                    }
                    _ => todo!(),
                }
            }

            region.append_block(block);

            let function = func::func(
                &context,
                StringAttribute::new(&context, &id.0),
                TypeAttribute::new(FunctionType::new(&context, &[], &[]).into()),
                region,
                &[(
                    Identifier::new(&context, "llvm.emit_c_interface"),
                    Attribute::unit(&context),
                )],
                location,
            );

            module.body().append_operation(function);
        }
    }

    // let function = {
    //     let region = Region::new();
    //     let block = Block::new(&[
    //         (integer_type.into(), location),
    //         (integer_type.into(), location),
    //     ]);
    //     let arg1 = block.argument(0).unwrap().into();
    //     let arg2 = block.argument(1).unwrap().into();

    //     let sum = block.append_operation(arith::addi(arg1, arg2, location));

    //     block.append_operation(func::r#return(&[sum.result(0).unwrap().into()], location));

    //     region.append_block(block);
    //     func::func(
    //         &context,
    //         StringAttribute::new(&context, "add"),
    //         TypeAttribute::new(
    //             FunctionType::new(
    //                 &context,
    //                 &[integer_type.into(), integer_type.into()],
    //                 &[integer_type.into()],
    //             )
    //             .into(),
    //         ),
    //         region,
    //         &[(
    //             Identifier::new(&context, "llvm.emit_c_interface"),
    //             Attribute::unit(&context),
    //         )],
    //         location,
    //     )
    // };

    let printf_decl = llvm::func(
        &context,
        StringAttribute::new(&context, "printf"),
        TypeAttribute::new(
            llvm::r#type::function(
                IntegerType::new(&context, 32).into(),
                &[llvm::r#type::pointer(
                    IntegerType::new(&context, 8).into(),
                    0,
                )],
                true,
            )
            .into(),
            // FunctionType::new(&context, &[r#type::Type::none(&context)], &[]).into(),
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

    // let region = Region::new();
    // let block = Block::new(&[(
    //     llvm::r#type::pointer(IntegerType::new(&context, 8).into(), 0).into(),
    //     location,
    // )]);

    // let arg1 = block.argument(0).unwrap().into();
    // unsafe {
    //     let res = block.append_operation(
    //         OperationBuilder::new("llvm.call", location)
    //             .add_operands(&[arg1])
    //             .add_attributes(&[(
    //                 Identifier::new(&context, "callee"),
    //                 FlatSymbolRefAttribute::new(&context, "printf").into(),
    //             )])
    //             .add_results(&[IntegerType::new(&context, 32).into()])
    //             .build(),
    //     );
    //     block.append_operation(llvm::r#return(
    //         Some(res.result(0).unwrap().into()),
    //         location,
    //     ));
    // }

    // region.append_block(block);
    // let print_decl = llvm::func(
    //     &context,
    //     StringAttribute::new(&context, "print"),
    //     TypeAttribute::new(
    //         llvm::r#type::function(
    //             IntegerType::new(&context, 32).into(),
    //             &[llvm::r#type::pointer(IntegerType::new(&context, 8).into(), 0).into()],
    //             false,
    //         )
    //         .into(),
    //         // FunctionType::new(&context, &[r#type::Type::none(&context)], &[]).into(),
    //     ),
    //     region,
    //     &[(
    //         Identifier::new(&context, "llvm.emit_c_interface"),
    //         Attribute::unit(&context),
    //     )],
    //     location,
    // );

    module.body().append_operation(printf_decl);
    // module.body().append_operation(function);
    // module.body().append_operation(print_decl);

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

    println!("module {:?}", module.as_operation());
    let mut result: i32 = 4;

    let mut val = std::ffi::CString::new("jj").unwrap();

    let mut ptr = val.as_ptr();

    let engine = ExecutionEngine::new(
        &module,
        0,
        &["/nix/store/46m4xx889wlhsdj72j38fnlyyvvvvbyb-glibc-2.37-8/lib/libc.so.6"],
        true,
    );

    engine.dump_to_object_file("llvmtest.ir");

    unsafe {
        engine
            .invoke_packed(
                "main",
                &mut [ptr as *mut (), &mut result as *mut i32 as *mut ()],
            )
            .unwrap();
    };
}

fn parse_assignment(assignment: Pair<Rule>) -> Result<TypedAst, Box<dyn std::error::Error>> {
    let mut inner_rules = assignment.into_inner();

    let identifier = inner_rules.next().unwrap();

    let expression = inner_rules.next().unwrap();

    let expression = parse_expression(expression);

    let assignment = TypedAst::Assignment(
        TSIdentifier(identifier.as_str().into()),
        expression.unwrap(),
    );

    Ok(assignment)
}

fn parse_expression(expression: Pair<Rule>) -> Result<TSExpression, Box<dyn std::error::Error>> {
    let inner_rules = expression.clone().into_inner().next().unwrap();

    let typed_exp = match expression.as_rule() {
        Rule::string => TSExpression::Value(TSValue::String(inner_rules.as_str().into())),
        Rule::identifier => TSExpression::Value(TSValue::Variable(inner_rules.as_str().into())),
        Rule::call => parse_fn_call(expression)?,
        _ => panic!("Got unexpected expression: {:?}", expression.as_rule()),
    };

    Ok(typed_exp)
}

fn parse_fn_call(call_expression: Pair<Rule>) -> Result<TSExpression, Box<dyn std::error::Error>> {
    let mut inner = call_expression.clone().into_inner().into_iter();

    println!("inner {call_expression:?}");
    let id = inner.next().unwrap();
    let args = inner.map(|arg| parse_expression(arg).unwrap()).collect();

    Ok(TSExpression::Call(
        TSIdentifier(id.as_str().to_string()),
        args,
    ))
}

pub fn load_all_dialects(context: &Context) {
    let registry = DialectRegistry::new();
    register_all_dialects(&registry);
    context.append_dialect_registry(&registry);
    context.load_all_available_dialects();
}

pub fn create_test_context() -> Context {
    let context = Context::new();

    context.attach_diagnostic_handler(|diagnostic| {
        eprintln!("{}", diagnostic);
        true
    });

    load_all_dialects(&context);
    register_all_llvm_translations(&context);

    context
}

#[test]
fn invoke_packed() {
    let registry = DialectRegistry::new();
    register_all_dialects(&registry);
    let context = Context::new();
    context.append_dialect_registry(&registry);
    context.get_or_load_dialect("func");
    context.get_or_load_dialect("arith");
    register_all_llvm_translations(&context);

    let location = Location::unknown(&context);
    let mut module = Module::new(location);

    let integer_type = IntegerType::new(&context, 64);

    let function = {
        let region = Region::new();
        let block = Block::new(&[
            (integer_type.into(), location),
            (integer_type.into(), location),
        ]);
        let arg1 = block.argument(0).unwrap().into();
        let arg2 = block.argument(1).unwrap().into();

        let sum = block.append_operation(arith::addi(arg1, arg2, location));

        block.append_operation(func::r#return(&[sum.result(0).unwrap().into()], location));

        region.append_block(block);
        func::func(
            &context,
            StringAttribute::new(&context, "add"),
            TypeAttribute::new(
                FunctionType::new(
                    &context,
                    &[integer_type.into(), integer_type.into()],
                    &[integer_type.into()],
                )
                .into(),
            ),
            region,
            &[(
                Identifier::new(&context, "llvm.emit_c_interface"),
                Attribute::unit(&context),
            )],
            location,
        )
    };

    module.body().append_operation(function);

    assert!(module.as_operation().verify());

    let pass_manager = pass::PassManager::new(&context);
    register_all_passes();
    pass_manager.enable_verifier(true);
    pass_manager.add_pass(pass::conversion::create_control_flow_to_llvm());
    pass_manager.add_pass(pass::conversion::create_func_to_llvm());
    pass_manager.add_pass(pass::conversion::create_index_to_llvm_pass());
    pass_manager.add_pass(pass::conversion::create_mem_ref_to_llvm());
    pass_manager.add_pass(pass::conversion::create_reconcile_unrealized_casts());

    pass_manager
        .nested_under("func.func")
        .add_pass(pass::conversion::create_arith_to_llvm());
    pass_manager.run(&mut module).unwrap();

    let engine = ExecutionEngine::new(&module, 2, &[], false);

    let mut argument1: i64 = 2;
    let mut argument2: i64 = 4;
    let mut result: i64 = -1;

    unsafe {
        engine
            .invoke_packed(
                "add",
                &mut [
                    &mut argument1 as *mut i64 as *mut (),
                    &mut argument2 as *mut i64 as *mut (),
                    &mut result as *mut i64 as *mut (),
                ],
            )
            .unwrap();
    };

    assert_eq!(result, 6);
}
