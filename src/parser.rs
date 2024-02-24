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
    Operation(Operation),
    If(IfStatement),
    While(While),
    Assign(Assign),
    Return(Return),
    Array(Array),
    ArrayLookup(ArrayLookup),
}

#[derive(Debug, Clone)]
pub struct ArrayLookup {
    pub array_identifier: TSIdentifier,
    pub index_expression: Box<TSExpression>,
}

#[derive(Debug, Clone)]
pub struct Array {
    pub items: Vec<TSExpression>,
}

#[derive(Debug, Clone)]
pub struct Return {
    pub expression: Option<Box<TSExpression>>,
}

#[derive(Debug, Clone)]
pub struct Assign {
    pub id: TSIdentifier,
    pub expression: Box<TSExpression>,
}

#[derive(Debug, Clone)]
pub struct While {
    pub condition: Box<TSExpression>,
    pub block: TSBlock,
}

#[derive(Debug, Clone)]
pub struct TSBlock {
    pub statements: Vec<TypedAst>,
}

impl TSBlock {
    fn new(statements: Vec<TypedAst>) -> Self {
        Self { statements }
    }
}

#[derive(Debug, Clone)]
pub struct IfStatement {
    pub condition: Box<TSExpression>,
    pub then_block: TSBlock,
    pub else_block: Option<TSBlock>,
}

#[derive(Debug, Clone)]
pub enum Operation {
    Binary(Box<TSExpression>, Operator, Box<TSExpression>),
}

#[derive(Debug, Clone)]
pub enum Operator {
    Addition,
    Subtraction,
    Division,
    Multiplication,
    Equality,
    Inequality,
    GreaterThanOrEqual,
    LessThanOrEqual,
    GreaterThan,
    LessThan,
}

#[derive(Debug, Clone)]
pub enum TSValue {
    String(String),
    Variable(TSIdentifier),
    Number,
    Integer(i32),
    Boolean(bool),
}

#[derive(Debug, Clone)]
pub enum TSType {
    String,
    StringLiteral,
    SignedInteger,
    UnsignedInteger,
    Boolean,
    Function,
    Named(TSIdentifier),
    Array(Box<TSType>, usize),
    Pointer,
}

#[derive(Debug, Clone, PartialEq, PartialOrd, Eq, Hash)]
pub enum FunctionKeyword {
    LlvmExtern,
    Normal,
}

impl TryFrom<String> for FunctionKeyword {
    type Error = anyhow::Error;

    fn try_from(value: String) -> std::result::Result<Self, Self::Error> {
        Ok(match value.as_str().trim() {
            "extern fn" => FunctionKeyword::LlvmExtern,
            "fn" => FunctionKeyword::Normal,
            _ => bail!("invalid function keyword: {}", value),
        })
    }
}

#[derive(Debug, Clone, PartialEq, PartialOrd, Eq, Hash)]
pub struct TSIdentifier(pub String);

#[derive(Debug, Clone)]
pub enum TypedAst {
    Expression(TSExpression),
    Assignment(TSIdentifier, TSExpression),
    Function {
        keywords: Vec<FunctionKeyword>,
        id: TSIdentifier,
        arguments: Vec<FunctionArg>,
        body: Option<Vec<TypedAst>>,
        return_type: Option<TSType>,
    },
    StructType(TSStructType),
}

#[derive(Debug, Clone)]
pub struct TSStructType {
    pub identifier: TSIdentifier,
    pub fields: Vec<TSStructField>,
}

#[derive(Debug, Clone)]
pub struct TSStructField {
    pub field_name: TSIdentifier,
    pub field_type: TSType,
}

#[derive(Debug, Clone)]
pub struct FunctionArg {
    pub name: TSIdentifier,
    pub r#type: Option<TSType>,
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

fn parse_if(rule: Pair<Rule>) -> Result<IfStatement> {
    let mut inner = if let Rule::r#if_else = rule.as_rule() {
        rule.into_inner()
    } else {
        bail!("expected an if rule got {rule:#?}");
    };

    let condition = parse_expression(inner.next().unwrap())?;
    let then_block_statements = inner
        .next()
        .unwrap()
        .into_inner()
        .into_iter()
        .map(parse_statement)
        .collect::<Result<Vec<TypedAst>>>()?;

    let else_block_statements = if let Some(inner) = inner.next() {
        Some(
            inner
                .into_inner()
                .into_iter()
                .map(parse_statement)
                .collect::<Result<Vec<TypedAst>>>()?,
        )
    } else {
        None
    };

    let then_block = TSBlock::new(then_block_statements);
    let else_block = else_block_statements.map(TSBlock::new);

    Ok(IfStatement {
        condition: Box::new(condition),
        then_block,
        else_block,
    })
}

fn parse_struct_decl(decl: Pair<Rule>) -> Result<TypedAst> {
    let mut decl = decl.into_inner();

    let identifier = TSIdentifier(decl.next().unwrap().as_str().to_string());

    let fields = decl
        .map(parse_struct_field_declaration)
        .collect::<Result<Vec<TSStructField>>>()?;

    Ok(TypedAst::StructType(TSStructType { identifier, fields }))
}

fn parse_struct_field_declaration(decl: Pair<Rule>) -> Result<TSStructField> {
    let mut decl = decl.into_inner();

    let field_name = TSIdentifier(decl.next().unwrap().as_str().to_string());

    let field_type = parse_type(decl.next().unwrap())?;

    Ok(TSStructField {
        field_name,
        field_type,
    })
}

fn parse_type(ty: Pair<Rule>) -> Result<TSType> {
    let mut inner = ty.into_inner();

    let next = inner.next().unwrap();
    Ok(match next.as_rule() {
        Rule::signed_integer => TSType::SignedInteger,
        Rule::unsigned_integer => TSType::UnsignedInteger,
        Rule::array_type => {
            let mut next_inner = next.into_inner();
            let item_type = parse_type(next_inner.next().unwrap())?;
            let len = next_inner.next().unwrap().as_str().parse::<usize>()?;
            TSType::Array(item_type.into(), len)
        }
        Rule::string_type => TSType::StringLiteral,
        Rule::named_type => TSType::Named(TSIdentifier(
            next.into_inner().next().unwrap().as_str().to_string(),
        )),
        Rule::pointer => TSType::Pointer,
        _ => bail!("expected a type rule got: {:?}", next),
    })
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

    let next = decl.next().unwrap();

    let keywords = if let Rule::functionType = next.as_rule() {
        vec![FunctionKeyword::try_from(next.as_str().to_string())?]
    } else {
        Vec::new()
    };

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

    let return_type = if let Some(Rule::r#type) = next.clone().map(|next| next.as_rule()) {
        let ty = parse_type(next.unwrap())?;
        next = decl.next();
        Some(ty)
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

    Ok(TypedAst::Function {
        keywords,
        id: identifer,
        arguments: function_args,
        body,
        return_type,
    })
}

fn parse_fn_arg(arg: Pair<Rule>) -> Result<FunctionArg> {
    let mut inner_rules = arg.into_inner();

    Ok(FunctionArg {
        name: TSIdentifier(inner_rules.next().unwrap().as_str().to_string()),
        r#type: inner_rules.next().map(|ty_id| parse_type(ty_id).unwrap()),
    })
}

fn parse_assignment(assignment: Pair<Rule>) -> Result<TypedAst> {
    let mut inner_rules = assignment.into_inner();

    let identifier = inner_rules.next().unwrap();

    let expression = inner_rules.next().unwrap();

    let expression = parse_expression(expression);

    let assignment = TypedAst::Assignment(
        TSIdentifier(identifier.as_str().trim().into()),
        expression.unwrap(),
    );

    Ok(assignment)
}

fn parse_statement(statement: Pair<Rule>) -> Result<TypedAst> {
    Ok(match statement.as_rule() {
        Rule::assignment => parse_assignment(statement)?,
        Rule::call
        | Rule::structInit
        | Rule::string
        | Rule::if_else
        | Rule::while_loop
        | Rule::r#return
        | Rule::assign => TypedAst::Expression(parse_expression(statement)?),
        Rule::function => parse_function_decl(statement)?,
        _ => bail!("Recieved unexpected rule: {:?}", statement),
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
        Rule::identifier => TSExpression::Value(TSValue::Variable(TSIdentifier(
            expression.as_str().trim().into(),
        ))),
        Rule::call => parse_fn_call(expression)?,
        Rule::structInit => parse_struct_init(expression)?,
        Rule::structFieldRef => parse_struct_field_ref(expression)?,
        Rule::integer => TSExpression::Value(parse_integer(expression)?),
        Rule::reference => {
            TSExpression::Value(parse_string(expression.into_inner().next().unwrap())?)
        }
        Rule::operation => TSExpression::Operation(parse_operation(expression)?),
        Rule::boolean => TSExpression::Value(parse_boolean(expression)?),
        Rule::r#if_else => TSExpression::If(parse_if(expression)?),
        Rule::while_loop => TSExpression::While(parse_while(expression)?),
        Rule::assign => TSExpression::Assign(parse_assign(expression)?),
        Rule::r#return => TSExpression::Return(parse_return(expression)?),
        Rule::array => TSExpression::Array(parse_array(expression)?),
        Rule::array_lookup => TSExpression::ArrayLookup(parse_array_lookup(expression)?),
        _ => panic!("Got unexpected expression: {:?}", expression.as_rule()),
    };

    Ok(typed_exp)
}

fn parse_array_lookup(expression: Pair<'_, Rule>) -> Result<ArrayLookup> {
    let mut inner = if let Rule::array_lookup = expression.as_rule() {
        expression.into_inner()
    } else {
        bail!("expected array lookup rule found {}", expression.as_str())
    };

    let Some(array_identifier) = inner
        .next()
        .map(|identifer| TSIdentifier(identifer.as_str().to_string()))
    else {
        bail!("missing array identifier")
    };

    let index = if let Some(index) = inner.next() {
        parse_expression(index)?
    } else {
        bail!("missing array index")
    };

    Ok(ArrayLookup {
        array_identifier: array_identifier,
        index_expression: index.into(),
    })
}

fn parse_array(expression: Pair<'_, Rule>) -> Result<Array> {
    let mut inner = if let Rule::array = expression.as_rule() {
        expression.into_inner()
    } else {
        bail!("expected array rule found {}", expression.as_str())
    };

    let items = inner
        .into_iter()
        .map(parse_expression)
        .collect::<Result<Vec<TSExpression>>>()?;

    Ok(Array {
        items: items.into(),
    })
}

fn parse_return(expression: Pair<'_, Rule>) -> Result<Return> {
    let mut inner = if let Rule::r#return = expression.as_rule() {
        expression.into_inner()
    } else {
        bail!("expected return rule found {}", expression.as_str());
    };

    let expression = if let Some(next) = inner.next() {
        Some(parse_expression(next)?.into())
    } else {
        None
    };

    Ok(Return { expression })
}

fn parse_assign(expression: Pair<'_, Rule>) -> Result<Assign> {
    let mut inner = if let Rule::assign = expression.as_rule() {
        expression.into_inner()
    } else {
        bail!("expected assign rule found {}", expression.as_str())
    };

    let id: TSIdentifier = TSIdentifier(inner.next().unwrap().as_str().trim().to_string());

    let expression = parse_expression(inner.next().unwrap())?;

    Ok(Assign {
        id,
        expression: Box::new(expression),
    })
}

fn parse_while(expression: Pair<'_, Rule>) -> Result<While> {
    let mut inner = if let Rule::while_loop = expression.as_rule() {
        expression.into_inner()
    } else {
        bail!(
            "expected the while rule, found {:?} instead",
            expression.as_rule()
        )
    };

    let condition = parse_expression(inner.next().unwrap())?;

    let block = TSBlock::new(
        inner
            .next()
            .unwrap()
            .into_inner()
            .into_iter()
            .map(parse_statement)
            .collect::<Result<Vec<TypedAst>>>()?,
    );

    Ok(While {
        condition: condition.into(),
        block,
    })
}

fn parse_boolean(expression: Pair<Rule>) -> Result<TSValue> {
    Ok(match expression.into_inner().next().unwrap().as_rule() {
        Rule::r#true => TSValue::Boolean(true),
        Rule::r#false => TSValue::Boolean(false),
        r => bail!("expected either false or true but got rule: {r:#?}"),
    })
}

fn parse_operation(expression: Pair<Rule>) -> Result<Operation> {
    let mut inner = if let Rule::operation = expression.as_rule() {
        expression.into_inner()
    } else {
        bail!("expected operation rule got {:?}", expression);
    };

    let first_operand = parse_expression(inner.next().unwrap())?;

    let operator = parse_operator(inner.next().unwrap())?;

    let second_operand = parse_expression(inner.next().unwrap())?;

    Ok(Operation::Binary(
        first_operand.into(),
        operator,
        second_operand.into(),
    ))
}

fn parse_operator(expression: Pair<Rule>) -> Result<Operator> {
    Ok(match expression.as_rule() {
        Rule::addition => Operator::Addition,
        Rule::subtraction => Operator::Subtraction,
        Rule::division => Operator::Division,
        Rule::multiplication => Operator::Multiplication,
        Rule::equal => Operator::Equality,
        Rule::not_equal => Operator::Inequality,
        Rule::greater_than => Operator::GreaterThan,
        Rule::less_than => Operator::LessThan,
        Rule::greater_than_or_equal => Operator::GreaterThanOrEqual,
        Rule::less_than_or_equal => Operator::LessThanOrEqual,
        _ => bail!("expected an infix operator but got: {:?}", expression),
    })
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
        Ok(TSValue::Integer(integer.as_str().trim().parse()?))
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
