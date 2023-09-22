use anyhow::Result;
use std::collections::HashMap;

use crate::parser::{self, Ast, TSExpression, TSIdentifier, TSValue};

#[derive(Debug, Clone)]
pub enum Type {
    Struct(Vec<(TSIdentifier, Type)>),
    Function(Vec<(TSIdentifier, Option<Type>)>, Option<TSIdentifier>),
    String,
}

#[derive(Debug, Clone)]
pub enum TypedExpression {
    Value(TSValue, Type),
    Call(TSIdentifier, Vec<TypedExpression>),
    Struct(TSIdentifier, Vec<TypedExpression>),
    StructFieldRef(TSIdentifier, TSIdentifier),
}

#[derive(Debug, Clone)]
pub enum TypedAst {
    Expression(TypedExpression),
    Assignment(TSIdentifier, TypedExpression, Option<Type>),
    Decl(Decl),
}

#[derive(Debug, Clone)]
pub enum Decl {
    Struct(TSIdentifier, Vec<(TSIdentifier, Type)>),
    Function(
        TSIdentifier,
        Vec<(TSIdentifier, Option<Type>)>,
        Option<TSIdentifier>,
    ),
}

#[derive(Debug, Clone)]
pub struct TypedAstBuilder {
    types: HashMap<TSIdentifier, Type>,
}

#[derive(Debug, Clone)]
pub struct TypedProgram {
    types: HashMap<TSIdentifier, Type>,
    ast: Vec<TypedAst>,
}

pub fn type_ast(ast: Ast) -> Result<TypedProgram> {
    let typed_ast = ast
        .0
        .into_iter()
        .map(|node| {
            Ok(match node {
                parser::TypedAst::Expression(exp) => TypedAst::Expression(type_expression(exp)?),
                parser::TypedAst::StructType(struct_id, fields) => TypedAst::Decl(Decl::Struct(
                    struct_id,
                    fields.into_iter().map(|f| (f, Type::String)).collect(),
                )),
                parser::TypedAst::Assignment(var_id, init_expression) => {
                    TypedAst::Assignment(var_id, type_expression(init_expression)?, None)
                }
                parser::TypedAst::Function(function_id, fields, return_type) => {
                    TypedAst::Decl(Decl::Function(
                        function_id,
                        fields.into_iter().map(|f| (f, None)).collect(),
                        None,
                    ))
                }
            })
        })
        .collect::<Result<Vec<TypedAst>>>()?;

    let mut types: HashMap<TSIdentifier, Type> = HashMap::new();
    for node in typed_ast {
        match node {
            TypedAst::Decl(decl) => {
                match decl {
                    Decl::Struct(id, fields) => types.insert(id, Type::Struct(fields)),
                    Decl::Function(id, fields, return_type) => {
                        types.insert(id, Type::Function(fields, return_type))
                    }
                };
            }

            _ => (),
        }
    }

    Ok(TypedProgram {
        types: HashMap::new(),
        ast: typed_ast,
    })
}

fn type_expression(exp: TSExpression) -> Result<TypedExpression> {
    Ok(match exp {
        TSExpression::Struct(type_id, fields) => TypedExpression::Struct(
            type_id,
            fields
                .into_iter()
                .map(|f| Ok(type_expression(f)?))
                .collect::<Result<Vec<TypedExpression>>>()?,
        ),
        TSExpression::Value(val) => match val.clone() {
            TSValue::String(string) => TypedExpression::Value(val, Type::String),
            _ => todo!("missing type expression for {:?}", val),
        },
        TSExpression::Call(function_id, arguments) => TypedExpression::Call(
            function_id,
            arguments
                .into_iter()
                .map(|arg| Ok(type_expression(arg)?))
                .collect::<Result<Vec<TypedExpression>>>()?,
        ),
        TSExpression::StructFieldRef(struct_id, field_id) => {
            TypedExpression::StructFieldRef(struct_id, field_id)
        }
    })
}
