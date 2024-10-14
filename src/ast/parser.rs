use anyhow::{bail, Result};
use pest::{
    iterators::{Pair, Pairs},
    Parser,
};
use pest_derive::Parser;

use crate::ast::{
    identifiers::DeclarationID,
    nodes::{AccessModes, FunctionKeyword, Identifier},
};

use super::{
    declarations::ModuleDeclaration,
    identifiers::{ExpressionID, FunctionDeclarationID, StatementID, StructDeclarationID},
    nodes::{
        Assignment, Block, Call, Expression, FunctionArg, FunctionDeclaration, Integer, Return,
        StructDeclaration, StructField, StructInit, Type, Value, Operation, Operator
    },
    Ast, NodeDatabase,
};
use tracing::debug;

#[derive(Parser)]
#[grammar = "typed_script.pest"]
struct TSParser;

struct AstBuilder {
    db: NodeDatabase,
    ast: Ast,
}

impl AstBuilder {
    fn new() -> Self {
        Self {
            db: NodeDatabase::default(),
            ast: Ast::new()
        }
    }
}

pub fn parse(input: &str) -> Result<(Ast, NodeDatabase, Vec<String>)> {
    let program = TSParser::parse(Rule::program, &input)?;
    let mut builder = AstBuilder::new();
    parse_program(program, &mut builder)
}

fn parse_program(
    program: Pairs<'_, Rule>,
    mut builder: &mut AstBuilder,
) -> Result<(Ast, NodeDatabase, Vec<String>)> {
    let mut module = ModuleDeclaration::new(Identifier::new("main".to_string()));

    for rule in program.into_iter() {
        let id = match rule.as_rule() {
            Rule::program => todo!(),
            Rule::function => {
                let id = parse_function_decl(builder, rule)?;
                DeclarationID::FunctionDeclaration(id)
            }
            Rule::r#struct => {
                let id = parse_struct_decl(builder, rule)?;
                DeclarationID::StructDeclaration(id)
            }
            Rule::EOI => break,
            _ => panic!("unexpected rule {:?}", rule.as_rule()),
        };
        module.declare(id);
    }

    let module_id = builder.db.new_module_declaration(module);
    builder.ast.modules.push(module_id);

    Ok((builder.ast.clone(), builder.db.clone(), Vec::new()))
}

fn parse_struct_decl(
    builder: &mut AstBuilder,
    rule: pest::iterators::Pair<'_, Rule>,
) -> Result<StructDeclarationID> {
    let mut decl = rule.into_inner();

    let identifier = Identifier::new(decl.next().unwrap().as_str().to_string());

    let fields = decl
        .map(parse_struct_field_declaration)
        .collect::<Result<Vec<StructField>>>()?;

    Ok(builder
        .db
        .new_struct_declaration(StructDeclaration { identifier, fields }))
}

fn parse_struct_field_declaration(decl: Pair<Rule>) -> Result<StructField> {
    let mut decl = decl.into_inner();

    let identifier = Identifier::new(decl.next().unwrap().as_str().to_string());

    let r#type = parse_type(decl.next().unwrap())?;

    Ok(StructField { identifier, r#type })
}

fn parse_function_decl(
    builder: &mut AstBuilder,
    rule: Pair<Rule>,
) -> Result<FunctionDeclarationID> {
    let mut decl = rule.into_inner();
    let next = decl.next().unwrap();

    let keywords = if let Rule::functionType = next.as_rule() {
        vec![FunctionKeyword::try_from(next.as_str().to_string())?]
    } else {
        Vec::new()
    };

    let identifier = Identifier::new(decl.next().unwrap().as_str().to_string());

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
        let body = next
            .map(|next| next.into_inner())
            .unwrap()
            .map(|statement| parse_statement(builder, statement))
            .collect::<Result<Vec<StatementID>>>()?;
        Some(builder.db.new_block(Block::new(body)))
    } else {
        None
    };

    Ok(builder.db.new_function_declaration(FunctionDeclaration {
        keywords,
        identifier,
        arguments: function_args,
        body,
        return_type,
    }))
}

fn parse_statement(
    builder: &mut AstBuilder,
    statement: Pair<Rule>,
) -> Result<StatementID, anyhow::Error> {
    Ok(match statement.as_rule() {
        Rule::function => parse_function_decl(builder, statement)?.into(),
        Rule::r#struct => parse_struct_decl(builder, statement)?.into(),
        Rule::call
        | Rule::structInit
        | Rule::string
        | Rule::if_else
        | Rule::while_loop
        | Rule::r#return
        | Rule::assignment
        | Rule::assign => parse_expression(builder, statement)?.into(),
        _ => bail!("Recieved unexpected rule: {:?}", statement),
    })
}

fn parse_expression(builder: &mut AstBuilder, pair: Pair<Rule>) -> Result<ExpressionID> {
    let expression = match pair.as_rule() {
        Rule::string => Expression::Value(parse_string(pair)?),
        Rule::assignment => Expression::Assignment(parse_assignment(builder, pair)?),
        Rule::identifier => Expression::Value(Value::Variable(Identifier::new(
            pair.as_str().trim().into(),
        ))),
        Rule::call => Expression::Call(parse_fn_call(builder, pair)?),
        Rule::structInit => Expression::Struct(parse_struct_init(builder, pair)?),
        // Rule::structFieldRef => parse_struct_field_ref(expression)?,
        Rule::integer => Expression::Value(Value::Integer(parse_integer(pair)?)),
        // Rule::reference => {
        //     Expression::Value(parse_string(expression.into_inner().next().unwrap())?)
        // }
        Rule::operation => Expression::Operation(parse_operation(builder, pair)?),
        // Rule::boolean => Expression::Value(parse_boolean(expression)?),
        // Rule::r#if_else => Expression::If(parse_if(expression)?),
        // Rule::while_loop => Expression::While(parse_while(expression)?),
        // Rule::assign => Expression::Assign(parse_assign(expression)?),
        Rule::r#return => Expression::Return(parse_return(builder, pair)?),
        // Rule::array => Expression::Array(parse_array(expression)?),
        // Rule::array_lookup => Expression::ArrayLookup(parse_array_lookup(expression)?),
        _ => panic!("Got unexpected expression: {:?}", pair.as_rule()),
    };

    let expression_id = builder.db.new_expression(expression);

    Ok(expression_id)
}

fn parse_operation(builder: &mut AstBuilder, pair: Pair<Rule>) -> Result<Operation> {
    let mut inner = if let Rule::operation = pair.as_rule() {
        pair.into_inner()
    } else {
        bail!("expected operation rule got {:?}", pair);
    };

    let first_operand = parse_expression(builder, inner.next().unwrap())?;

    let operator = parse_operator(inner.next().unwrap())?;

    let second_operand = parse_expression(builder, inner.next().unwrap())?;

    Ok(Operation::Binary(
        first_operand,
        operator,
        second_operand,
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

fn parse_return(builder: &mut AstBuilder, pair: Pair<Rule>) -> Result<Return> {
    let mut inner = if let Rule::r#return = pair.as_rule() {
        pair.into_inner()
    } else {
        bail!("expected return rule found {}", pair.as_str());
    };

    let expression_id = if let Some(next) = inner.next() {
        Some(parse_expression(builder, next)?.into())
    } else {
        None
    };

    Ok(Return {
        expression: expression_id,
    })
}

fn parse_struct_init(builder: &mut AstBuilder, pair: Pair<Rule>) -> Result<StructInit> {
    todo!()
}

fn parse_integer(integer: Pair<Rule>) -> Result<Integer> {
    if let Rule::integer = integer.as_rule() {
        let value = integer.as_str().trim().parse()?;
        Ok(Integer {
            value,
            signed: true,
            size: 32,
        })
    } else {
        bail!("expected string , got {:?}", integer.as_rule())
    }
}

fn parse_fn_call(builder: &mut AstBuilder, call_expression: Pair<Rule>) -> Result<Call> {
    let mut inner = call_expression.clone().into_inner().into_iter();

    let id = inner.next().unwrap();

    let args = inner.next().unwrap().into_inner().into_iter();

    let args = args
        .map(|arg| parse_expression(builder, arg).unwrap())
        .collect();


    let call = Call { function_id: Identifier(id.as_str().trim().to_string()),
        arguments: args,
    };

    Ok(call)
}

fn parse_assignment(builder: &mut AstBuilder, pair: Pair<'_, Rule>) -> Result<Assignment> {
    let mut inner_rules = pair.into_inner();

    let identifier = inner_rules.next().unwrap();

    let expression = inner_rules.next().unwrap();

    let expression = parse_expression(builder, expression);

    let assignment = Assignment {
        id: Identifier::new(identifier.as_str().trim().into()),
        expression: expression.unwrap(),
    };

    Ok(assignment)
}

fn parse_string(string: Pair<Rule>) -> Result<Value> {
    if let Rule::string = string.as_rule() {
        Ok(Value::String(string.into_inner().as_str().to_string()))
    } else {
        bail!("expected string , got {:?}", string.as_rule())
    }
}

fn parse_fn_arg(arg: Pair<Rule>) -> Result<FunctionArg> {
    let mut inner_rules = arg.into_inner();
    let n_rules = inner_rules.len();
    let Some(first_rule) = inner_rules.next() else {
        bail!("function argument was empty");
    };

    let access_mode = if let Rule::accessMode = first_rule.as_rule() {
        match first_rule
            .clone()
            .into_inner()
            .next()
            .map(|inner| inner.as_rule())
        {
            Some(Rule::letAccess) => AccessModes::Let,
            Some(Rule::ownedAccess) => AccessModes::Owned,
            Some(Rule::inoutAccess) => AccessModes::Inout,
            e @ _ => bail!("exptec to find an access found instead foud {:?}", e),
        }
    } else {
        AccessModes::default()
    };

    let name = if n_rules == 2 {
        Identifier::new(first_rule.as_str().to_string())
    } else {
        Identifier::new(inner_rules.next().unwrap().as_str().to_string())
    };

    Ok(FunctionArg {
        access_mode,
        name,
        r#type: inner_rules.next().map(|ty_id| parse_type(ty_id).unwrap()),
    })
}

fn parse_type(ty: Pair<Rule>) -> Result<Type> {
    let mut inner = ty.into_inner();

    let next = inner.next().unwrap();
    Ok(match next.as_rule() {
        Rule::signed_integer => Type::SignedInteger,
        Rule::unsigned_integer => Type::UnsignedInteger,
        Rule::array_type => {
            let mut next_inner = next.into_inner();
            let item_type = parse_type(next_inner.next().unwrap())?;
            let len = next_inner.next().unwrap().as_str().parse::<usize>()?;
            Type::Array(item_type.into(), len)
        }
        Rule::string_type => Type::StringLiteral,
        Rule::named_type => Type::Named(Identifier::new(
            next.into_inner().next().unwrap().as_str().to_string(),
        )),
        Rule::pointer => Type::Pointer,
        _ => bail!("expected a type rule got: {:?}", next),
    })
}

#[cfg(test)]
mod test {
    use super::*;
    use anyhow::Result;
    use rstest::rstest;
    use std::path::PathBuf;
    use tracing::debug;

    #[rstest]
    #[test_log::test]
    fn snapshop_ast_output(#[files("./test_programs/test_*.ts")] path: PathBuf) -> Result<()> {
        let input = std::fs::read_to_string(&path)?;
        let ast = parse(&input)?;
        debug!("input for parser:\n {input}");
        insta::assert_snapshot!(
            format!(
                "test_ast_snapshot_{}",
                path.file_name().unwrap().to_str().unwrap()
            ),
            format!("{}", ast.0.to_string(&ast.1))
        );
        Ok(())
    }
}
