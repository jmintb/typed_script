use pest::{iterators::Pair, Parser};
use pest_derive::{self, Parser};

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
