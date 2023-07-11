use pest::{iterators::Pair, Parser};
use pest_derive::{self, Parser};

use melior::{
    dialect::{arith, func, DialectRegistry},
    ir::{
        attribute::{StringAttribute, TypeAttribute},
        r#type::FunctionType,
        *,
    },
    utility::register_all_dialects,
    Context,
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
}

#[derive(Debug)]
pub struct TSIdentifier(String);

#[derive(Debug)]
pub enum TSAST {
    Value(TSValue),
    Expression(TSExpression),
    Assignment(TSIdentifier, TSExpression),
}

#[derive(Debug)]
pub enum TypedAst {
    Value(TSValue, TSType),
    Expression(TSExpression),
    Assignment(TSIdentifier, TSExpression),
}

fn main() {
    let parsed_res = TSParser::parse(Rule::program, "let myvar = \"test\"; myvar").unwrap();

    let mut ast: Vec<TypedAst> = vec![];

    for rule in parsed_res {
        let node = match rule.as_rule() {
            Rule::program => todo!(),
            Rule::expression => TypedAst::Expression(parse_expression(rule).unwrap()),
            Rule::assignment => parse_assignment(rule).unwrap(),
            _ => continue,
        };

        ast.push(node);
    }

    let registry = DialectRegistry::new();
    register_all_dialects(&registry);

    let context = Context::new();
    context.append_dialect_registry(&registry);
    context.load_all_available_dialects();

    let location = Location::unknown(&context);
    let module = Module::new(location);

    let index_type = Type::index(&context);

    module.body().append_operation(func::func(
        &context,
        StringAttribute::new(&context, "add"),
        TypeAttribute::new(
            FunctionType::new(&context, &[index_type, index_type], &[index_type]).into(),
        ),
        {
            let block = Block::new(&[(index_type, location), (index_type, location)]);

            let sum = block.append_operation(arith::addi(
                block.argument(0).unwrap().into(),
                block.argument(1).unwrap().into(),
                location,
            ));

            block.append_operation(func::r#return(&[sum.result(0).unwrap().into()], location));

            let region = Region::new();
            region.append_block(block);
            region
        },
        &[],
        location,
    ));

    assert!(module.as_operation().verify());
    println!("ast {:?}", ast);
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
