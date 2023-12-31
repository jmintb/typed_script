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
    Struct(TSIdentifier, Vec<TSExpression>),
    StructFieldRef(TSIdentifier, TSIdentifier),
}

#[derive(Debug, Clone)]
pub enum TSValue {
    String(String),
    Variable(TSIdentifier),
    Number,
    Integer(i32),
    Boolean,
}

#[derive(Debug, Clone)]
pub enum TSType {
    String,
    StringLiteral,
    Number,
    Boolean,
    Function,
}

#[derive(Debug, Clone, PartialEq, PartialOrd, Eq, Hash)]
pub struct TSIdentifier(pub String);

#[derive(Debug, Clone)]
pub enum TypedAst {
    Expression(TSExpression),
    Assignment(TSIdentifier, TSExpression),
    Function(
        TSIdentifier,
        Vec<FunctionArg>,
        Option<Vec<TypedAst>>,
        Option<TSIdentifier>,
    ),
    StructType(TSIdentifier, Vec<TSIdentifier>),
}

#[derive(Debug, Clone)]
pub struct FunctionArg {
    pub name: TSIdentifier,
    pub r#type: Option<TSIdentifier>,
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
            Rule::r#struct => parse_struct_decl(rule)?,
            Rule::structInit => TypedAst::Expression(parse_expression(rule)?),
            Rule::EOI => break,
            _ => panic!("unexpected rule {:?}", rule.as_rule()),
        };

        ast.push(node);
    }

    Ok(Ast(ast))
}

fn parse_struct_decl(decl: Pair<Rule>) -> Result<TypedAst> {
    let mut decl = decl.into_inner();

    let identifer = TSIdentifier(decl.next().unwrap().as_str().to_string());

    let fields = decl.map(|d| TSIdentifier(d.as_str().to_string())).collect();

    Ok(TypedAst::StructType(identifer, fields))
}

fn parse_struct_init(init: Pair<Rule>) -> Result<TSExpression> {
    let mut init = init.into_inner();

    let identifier = TSIdentifier(init.next().unwrap().as_str().to_string());
    let fields = init
        .map(|f| parse_expression(f))
        .collect::<Result<Vec<TSExpression>>>()?;

    Ok(TSExpression::Struct(identifier, fields))
}

fn parse_function_decl(decl: Pair<Rule>) -> Result<TypedAst> {
    let mut decl = decl.into_inner();

    let identifer = TSIdentifier(decl.next().unwrap().as_str().to_string());

    let mut next = decl.next();

    let function_args: Vec<FunctionArg> =
        if let Some(Rule::functionArgs) = next.clone().map(|next| next.as_rule()) {
            let args = next.clone().map(|next| next.into_inner()).unwrap();
            next = decl.next();
            args.map(parse_fn_arg)
                .collect::<Result<Vec<FunctionArg>>>()?
        } else {
            vec![]
        };

    let return_type = if let Some(Rule::identifier) = next.clone().map(|next| next.as_rule()) {
        next.clone()
            .map(|next| TSIdentifier(next.as_str().to_string()))
    } else {
        None
    };

    let body = if let Some(Rule::functionBody) = next.clone().map(|next| next.as_rule()) {
        Some(
            next.map(|next| next.into_inner())
                .unwrap()
                .map(|statement| parse_statement(statement))
                .collect::<Result<Vec<TypedAst>>>()?,
        )
    } else {
        None
    };

    Ok(TypedAst::Function(
        identifer,
        function_args,
        body,
        return_type,
    ))
}

fn parse_fn_arg(arg: Pair<Rule>) -> Result<FunctionArg> {
    let mut inner_rules = arg.into_inner();

    Ok(FunctionArg {
        name: TSIdentifier(inner_rules.next().unwrap().as_str().to_string()),
        r#type: inner_rules
            .next()
            .map(|ty_id| TSIdentifier(ty_id.as_str().to_string())),
    })
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

fn parse_statement(statement: Pair<Rule>) -> Result<TypedAst> {
    Ok(match statement.as_rule() {
        Rule::assignment => parse_assignment(statement)?,
        Rule::call | Rule::structInit | Rule::string => {
            TypedAst::Expression(parse_expression(statement)?)
        }
        Rule::function => parse_function_decl(statement)?,
        _ => bail!("Recieved unexpected rule: {:?}", statement.as_rule()),
    })
}

fn parse_struct_field_ref(sref: Pair<Rule>) -> Result<TSExpression> {
    let mut inner_rules = sref.into_inner();

    let struct_id = TSIdentifier(inner_rules.next().unwrap().as_str().into());
    let field_id = TSIdentifier(inner_rules.next().unwrap().as_str().into());

    Ok(TSExpression::StructFieldRef(struct_id, field_id))
}

fn parse_expression(expression: Pair<Rule>) -> Result<TSExpression> {
    let typed_exp = match expression.as_rule() {
        Rule::string => TSExpression::Value(parse_string(expression)?),
        Rule::identifier => {
            TSExpression::Value(TSValue::Variable(TSIdentifier(expression.as_str().into())))
        }
        Rule::call => parse_fn_call(expression)?,
        Rule::structInit => parse_struct_init(expression)?,
        Rule::structFieldRef => parse_struct_field_ref(expression)?,
        Rule::integer => TSExpression::Value(parse_integer(expression)?),
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

fn parse_integer(integer: Pair<Rule>) -> Result<TSValue> {
    if let Rule::integer = integer.as_rule() {
        Ok(TSValue::Integer(integer.as_str().parse()?))
    } else {
        bail!("expected string , got {:?}", integer.as_rule())
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
