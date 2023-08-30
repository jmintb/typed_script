use core::panic;

use anyhow::{bail, Result};
use pest::{iterators::Pair, Parser};
use pest_derive::Parser;

#[derive(Parser)]
#[grammar = "typed_script.pest"]
struct TSParser;

#[derive(Debug, Clone)]
pub enum TSExpression {
    Value(TSValue),
    Call(TSIdentifier, Vec<TSExpression>),
}

#[derive(Debug, Clone)]
pub enum TSValue {
    String(String),
    Variable(String),
    Number,
    Boolean,
}

#[derive(Debug, Clone)]
pub enum TSType {
    String,
    Number,
    Boolean,
    Function,
}

#[derive(Debug, Clone)]
pub struct TSIdentifier(pub String);

#[derive(Debug, Clone)]
pub enum TypedAst {
    Value(TSValue, TSType),
    Expression(TSExpression),
    Assignment(TSIdentifier, TSExpression),
    Function(TSIdentifier, Vec<TSIdentifier>, Vec<TypedAst>),
}

pub struct Ast(pub Vec<TypedAst>);

pub fn parse(input: &str) -> Result<Ast> {
    let program = TSParser::parse(Rule::program, &input)?;

    let mut ast: Vec<TypedAst> = vec![];

    for rule in program.into_iter() {
        let node = match rule.as_rule() {
            Rule::program => todo!(),
            Rule::expression => TypedAst::Expression(parse_expression(rule).unwrap()),
            Rule::assignment => parse_assignment(rule).unwrap(),
            Rule::function => parse_function_decl(rule)?,
            Rule::EOI => break,
            _ => panic!("unexpected rule {:?}", rule.as_rule()),
        };

        ast.push(node);
    }

    Ok(Ast(ast))
}

fn parse_function_decl(decl: Pair<Rule>) -> Result<TypedAst> {
    let mut decl = decl.into_inner();

    let identifer = TSIdentifier(decl.next().unwrap().as_str().to_string());

    let mut next = decl.next().unwrap();

    let function_args: Vec<TSIdentifier> = if let Rule::functionArgs = next.as_rule() {
        let args = next.into_inner();
        next = decl.next().unwrap();
        args.map(|p| TSIdentifier(p.into_inner().as_str().to_string()))
            .collect()
    } else {
        vec![]
    };

    let body = if let Rule::functionBody = next.as_rule() {
        next.into_inner()
            .map(|exp| TypedAst::Expression(parse_expression(exp).unwrap()))
            .collect()
    } else {
        bail!(
            "expected to find function body, found {:?} instead, in function declaration {}",
            next.as_rule(),
            identifer.0
        );
    };

    Ok(TypedAst::Function(identifer, function_args, body))
}

fn parse_assignment(assignment: Pair<Rule>) -> Result<TypedAst> {
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

fn parse_expression(expression: Pair<Rule>) -> Result<TSExpression> {
    let typed_exp = match expression.as_rule() {
        Rule::string => TSExpression::Value(parse_string(expression)?),
        Rule::identifier => TSExpression::Value(TSValue::Variable(expression.as_str().into())),
        Rule::call => parse_fn_call(expression)?,
        _ => panic!("Got unexpected expression: {:?}", expression.as_rule()),
    };

    Ok(typed_exp)
}

fn parse_string(string: Pair<Rule>) -> Result<TSValue> {
    if let Rule::string = string.as_rule() {
        Ok(TSValue::String(string.into_inner().as_str().to_string()))
    } else {
        bail!("expected string , got {:?}", string.as_rule())
    }
}

fn parse_fn_call(call_expression: Pair<Rule>) -> Result<TSExpression> {
    let mut inner = call_expression.clone().into_inner().into_iter();

    let id = inner.next().unwrap();

    let args = inner.next().unwrap().into_inner().into_iter();

    let args = args.map(|arg| parse_expression(arg).unwrap()).collect();

    Ok(TSExpression::Call(
        TSIdentifier(id.as_str().to_string()),
        args,
    ))
}
