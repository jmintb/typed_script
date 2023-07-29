use pest::{iterators::Pair, Parser};
use pest_derive::{self, Parser};

use melior::{
    dialect::{
        self, arith, func,
        llvm::{self, r#type::void},
        DialectRegistry,
    },
    ir::{
        attribute::{StringAttribute, TypeAttribute},
        r#type::{FunctionType, IntegerType},
        *,
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
    let parsed_res =
        TSParser::parse(Rule::program, "fn test () {  let myvar = \"test\"; myvar }").unwrap();

    let registry = DialectRegistry::new();
    register_all_dialects(&registry);
    let context = Context::new();
    context.append_dialect_registry(&registry);
    context.get_or_load_dialect("func");
    context.get_or_load_dialect("arith");
    register_all_llvm_translations(&context);

    let location = Location::unknown(&context);
    let mut module = Module::new(location);

    let mut ast: Vec<TypedAst> = vec![];

    for rule in parsed_res {
        let node = match rule.as_rule() {
            Rule::program => todo!(),
            Rule::expression => TypedAst::Expression(parse_expression(rule).unwrap()),
            Rule::assignment => parse_assignment(rule).unwrap(),
            Rule::function => {
                println!("function: {}", rule);

                let mut inner = rule.into_inner();

                let identifer = TSIdentifier(inner.next().unwrap().as_str().to_string());

                println!("id: {:?}", identifer);

                let mut fn_body = vec![];

                while let Some(body_exp) = inner.next() {
                    let node = match body_exp.as_rule() {
                        Rule::expression => {
                            TypedAst::Expression(parse_expression(body_exp).unwrap())
                        }
                        Rule::assignment => parse_assignment(body_exp).unwrap(),
                        _ => todo!(),
                    };

                    fn_body.push(node);
                }

                TypedAst::Function(identifer, fn_body)
            }
            _ => continue,
        };

        ast.push(node);
    }

    println!("ast: {:?}", ast);

    for node in ast {
        match node {
            TypedAst::Function(id, body) => {
               for node in ast {
                    
                } 
            }
            _ =>
        }
    }

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
    let mut inner_rules = expression.into_inner().next().unwrap();

    let typed_exp = match inner_rules.as_rule() {
        Rule::string => TSExpression::Value(TSValue::String(inner_rules.as_str().into())),
        Rule::identifier => TSExpression::Value(TSValue::Variable(inner_rules.as_str().into())),
        _ => todo!(),
    };

    Ok(typed_exp)
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
