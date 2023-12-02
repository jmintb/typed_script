use anyhow::Result;
use melior::{dialect::llvm, ir::r#type::IntegerType, Context};
use std::collections::HashMap;

use crate::parser::{self, Ast, TSExpression, TSIdentifier, TSValue};

#[derive(Debug, Clone)]
pub enum Type {
    Struct(Vec<(TSIdentifier, Type)>),
    Function(Vec<FunctionArg>, Option<Box<Type>>),
    Named(TSIdentifier),
    String,
    Unknown,
    Integer,
    Boolean,
    Pointer,
    Unit,
}

impl Type {
    pub fn as_mlir_type<'c>(&self, context: &'c Context) -> melior::ir::Type<'c> {
        match self {
            Type::Pointer => llvm::r#type::opaque_pointer(context),
            Type::String => llvm::r#type::opaque_pointer(context),
            Type::Integer => IntegerType::new(context, 32).into(),
            Type::Unit => llvm::r#type::void(context),
            _ => todo!("unimplemented return type"),
        }
    }
}

impl From<TSIdentifier> for Type {
    fn from(value: TSIdentifier) -> Self {
        match value.0.as_str() {
            "int" => Self::Integer,
            "string" => Self::String,
            "bool" => Self::Boolean,
            "ptr" => Self::Pointer,
            _ => Self::Named(value),
        }
    }
}

impl Default for Type {
    fn default() -> Self {
        Self::Unknown
    }
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
        Vec<FunctionArg>,
        Option<Vec<TypedAst>>,
        Option<Type>,
    ),
}

#[derive(Debug, Clone)]
pub struct FunctionArg {
    pub name: TSIdentifier,
    pub r#type: Type,
}

#[derive(Debug, Clone)]
pub struct TypedAstBuilder {
    types: HashMap<TSIdentifier, Type>,
}

#[derive(Debug, Clone)]
pub struct TypedProgram {
    pub types: HashMap<TSIdentifier, Type>,
    pub ast: Vec<TypedAst>,
}

fn ast_to_typed(node: parser::TypedAst) -> Result<TypedAst> {
    Ok(match node {
        parser::TypedAst::Expression(exp) => TypedAst::Expression(type_expression(exp)?),
        parser::TypedAst::StructType(struct_id, fields) => TypedAst::Decl(Decl::Struct(
            struct_id,
            fields.into_iter().map(|f| (f, Type::String)).collect(),
        )),
        parser::TypedAst::Assignment(var_id, init_expression) => {
            TypedAst::Assignment(var_id, type_expression(init_expression)?, None)
        }
        parser::TypedAst::Function(function_id, fields, body, return_type) => {
            TypedAst::Decl(Decl::Function(
                function_id,
                fields
                    .into_iter()
                    .map(|f| FunctionArg {
                        name: f.name,
                        r#type: f.r#type.map(|ty_id| Type::Named(ty_id)).unwrap_or_default(),
                    })
                    .collect(),
                body.map(|body| {
                    body.into_iter()
                        .map(ast_to_typed)
                        .collect::<Result<Vec<TypedAst>>>()
                        .unwrap()
                }),
                return_type.map(|return_type| return_type.into()),
            ))
        }
    })
}

pub fn type_ast(ast: Ast) -> Result<TypedProgram> {
    let typed_ast = ast
        .0
        .into_iter()
        .map(ast_to_typed)
        .collect::<Result<Vec<TypedAst>>>()?;

    let mut types: HashMap<TSIdentifier, Type> = HashMap::new();
    for node in typed_ast.clone() {
        match node {
            TypedAst::Decl(decl) => {
                match decl {
                    Decl::Struct(id, fields) => types.insert(id, Type::Struct(fields)),
                    Decl::Function(id, fields, body, return_type) => types.insert(
                        id,
                        Type::Function(
                            fields,
                            return_type.map(|return_type| Box::new(return_type)),
                        ),
                    ),
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
            TSValue::String(_) => TypedExpression::Value(val, Type::String),
            TSValue::Variable(_) => TypedExpression::Value(val, Type::Unknown),
            TSValue::Integer(_) => TypedExpression::Value(val, Type::Integer),
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
