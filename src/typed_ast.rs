use anyhow::{Result, bail};
use melior::{dialect::llvm, ir::r#type::IntegerType, Context};
use std::{collections::HashMap, fmt::Binary};

use crate::parser::{self, Ast, FunctionKeyword, TSExpression, TSIdentifier, TSValue, Operator};

#[derive(Debug, Clone)]
pub enum Type {
    Struct(Vec<(TSIdentifier, Type)>),
    Function(Vec<FunctionKeyword>, Vec<FunctionArg>, Box<Type>),
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
            Type::Struct(fields) => llvm::r#type::r#struct(
                &context,
                fields
                    .iter()
                    .map(|f| f.1.as_mlir_type(context))
                    .collect::<Vec<melior::ir::Type>>()
                    .as_slice(),
                true,
            ),
            _ => todo!("unimplemented type to mlir type {:?}", self),
        }
    }
}

impl From<TSIdentifier> for Type {
    fn from(value: TSIdentifier) -> Self {
        match value.0.as_str().trim() {
            "integer" => Self::Integer,
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
pub struct While {
    pub condition: Box<TypedExpression>,
    pub block: Block
}

#[derive(Debug, Clone)]
pub struct Assign {
    pub id: TSIdentifier,
    pub expression: Box<TypedExpression>
}

#[derive(Debug, Clone)]
pub enum TypedExpression {
    Value(TSValue, Type),
    Call(TSIdentifier, Vec<TypedExpression>),
    Struct(TSIdentifier, Vec<TypedExpression>),
    StructFieldRef(TSIdentifier, TSIdentifier),
    Operation(Box<Operation>),
    If(IfStatement),
    While(While),
    Assign(Assign),
}



impl TypedExpression {
    fn r#type(&self, types: &HashMap<TSIdentifier, Type>) -> Result<Type> {
       match self {
            Self::Value(_, r#type ) => Ok(r#type.clone()),
            Self::Call(type_id, _  ) => types.get(type_id).map(|expression_type| match expression_type.clone() {
               Type::Function(_, _, ref return_type ) => Ok((**return_type).clone()), 
                _ => bail!("expected to a function type for a call expression, instead found {:#?} for type id {}", expression_type, type_id.0)
            }).unwrap(),
            Self::Struct(type_id, _ ) => { types.get(type_id).map(|expression_type| match expression_type {
               Type::Struct(..) => Ok(expression_type.clone()), 
                _ => bail!("expected to a struct type, instead found {:#?} for type id {}", expression_type, type_id.0)
            }).unwrap()
            },
        Self::StructFieldRef( .. ) => Ok(Type::Unknown),
            Self::Operation(operation) => match operation.as_ref() {
                Operation::Binary(first_operand,_ ,_ ) => first_operand.r#type(types)
            } 
            Self::If(_) => Ok(Type::Unit),
            Self::While(_) => Ok(Type::Unit),
            Self::Assign(_) => Ok(Type::Unit),
         } 
    }
}

#[derive(Debug, Clone)]
pub enum TypedAst {
    Expression(TypedExpression),
    Assignment(Assignment),
    Decl(Decl),
}

#[derive(Debug, Clone)]
pub struct IfStatement {
    pub condition: Box<TypedExpression>,
    pub then_block: Block,
    pub else_block: Option<Block>,
}

#[derive(Debug, Clone)]
pub struct Block {
    pub statements: Vec<TypedAst>
}

#[derive(Debug, Clone)]
pub enum Decl {
    Struct(TSIdentifier, Vec<(TSIdentifier, Type)>),
    Function {
        keywords: Vec<FunctionKeyword>,
        id: TSIdentifier,
        arguments: Vec<FunctionArg>,
        body: Option<Vec<TypedAst>>,
        return_type: Type,
    },
}

#[derive(Debug, Clone)]
pub struct Assignment {
    pub id: TSIdentifier,
    pub expression: TypedExpression,
    pub typed_annotation: Option<Type>,
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
    pub variable_types: HashMap<TSIdentifier, Type>,
}

#[derive(Debug, Clone)]
pub enum Operation {
    Binary(TypedExpression, Operator, TypedExpression)
}

fn ast_to_typed(node: parser::TypedAst) -> Result<TypedAst> {
    Ok(match node {
        parser::TypedAst::Expression(exp) => TypedAst::Expression(type_expression(exp)?),
        parser::TypedAst::StructType(struct_id, fields) => TypedAst::Decl(Decl::Struct(
            struct_id,
            fields.into_iter().map(|f| (f, Type::String)).collect(),
        )),
        parser::TypedAst::Assignment(var_id, init_expression) => {
            let expression = type_expression(init_expression)?;
            
            TypedAst::Assignment(Assignment { id: var_id, expression, typed_annotation: None})
        }
        parser::TypedAst::Function {
            keywords,
            id,
            arguments,
            body,
            return_type,
        } => TypedAst::Decl(Decl::Function {
            keywords,
            id,
            arguments: arguments
                .into_iter()
                .map(|f| FunctionArg {
                    name: f.name,
                    r#type: f
                        .r#type
                        .map(|ty_id| match ty_id.0.as_str().trim() {
                            "integer" => Type::Integer,
                            "string" => Type::String,
                            _ => Type::Named(ty_id),
                        })
                        .unwrap_or_default(),
                })
                .collect(),
            body: body.map(|body| {
                body.into_iter()
                    .map(ast_to_typed)
                    .collect::<Result<Vec<TypedAst>>>()
                    .unwrap()
            }),
            return_type: return_type
                .map(|return_type| return_type.into())
                .unwrap_or(Type::Unit),
        }),
    })
}

fn type_if(if_statement: parser::IfStatement) -> Result<IfStatement> {
    Ok(IfStatement { condition: type_expression(*if_statement.condition)?.into(), then_block: type_block(if_statement.then_block)?, else_block: if let Some(block) = if_statement.else_block {
        Some(type_block(block)?)
    } else {
        None
    }   })
}

fn type_block(block: parser::TSBlock) -> Result<Block> {
    let typed_statements = block.statements.into_iter().map(ast_to_typed).collect::<Result<Vec<TypedAst>>>()?;

    Ok(Block { statements: typed_statements})
}

pub fn type_ast(ast: Ast) -> Result<TypedProgram> {
    let typed_ast = ast
        .0
        .into_iter()
        .map(ast_to_typed)
        .collect::<Result<Vec<TypedAst>>>()?;

    let mut types: HashMap<TSIdentifier, Type> = HashMap::new();
    let mut variable_types: HashMap<TSIdentifier, Type> = HashMap::new();
    let mut nodes = typed_ast.clone();

    loop {
        let Some(node) = nodes.pop() else {
            break;
        };

        match node {
            TypedAst::Decl(decl) => {
                match decl {
                    Decl::Struct(id, fields) => {
                        types.insert(id, Type::Struct(fields));
                    }
                    Decl::Function {
                        keywords,
                        id,
                        arguments,
                        body,
                        return_type,
                    } => {
                        types.insert(
                            id,
                            Type::Function(keywords, arguments, Box::new(return_type)),
                        );
                        if let Some(mut body) = body {
                            nodes.append(&mut body);
                        }
                    }
                };
            }

           _ => (),
        }
    }

    let mut nodes = typed_ast.clone();
      loop {
        let Some(node) = nodes.pop() else {
            break;
        };

        match node {
            TypedAst::Decl(decl) => {
                match decl {
                    Decl::Function {
                        body, ..
                    } => {
                        if let Some(mut body) = body {
                            nodes.append(&mut body);
                        }
                    }
                     _ => ()
                };
            }

            TypedAst::Assignment(Assignment { id, expression, typed_annotation }) => {
                let assignment_type = typed_annotation.unwrap_or(expression.r#type(&types)?);
                variable_types.insert(id, assignment_type);
            }
            _ => (),
        }
    }

    Ok(TypedProgram {
        types,
        ast: typed_ast,
        variable_types,
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
            TSValue::Boolean(_) => TypedExpression::Value(val, Type::Boolean ),
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

        TSExpression::Operation(operation) => TypedExpression::Operation(typed_operator(operation)?.into()),
        TSExpression::If(IfStatement) => TypedExpression::If(type_if(IfStatement)?),
        TSExpression::While(While) => TypedExpression::While(type_while(While)?),
        TSExpression::Assign(assign) => TypedExpression::Assign(type_assign(assign)?)
    })
}

fn type_assign(assign: parser::Assign) -> Result<Assign> {
    Ok(Assign { id: assign.id, expression: type_expression(*assign.expression)?.into()  })
}

fn type_while(r#while: parser::While) -> Result<While> {
    let condition = type_expression(*r#while.condition)?;
    let block = type_block(r#while.block)?;

    Ok(While { condition: condition.into(), block  })
}

fn typed_operator(operation: parser::Operation) -> Result<Operation> {
    Ok(match operation {
        parser::Operation::Binary(first_operand, operator, second_operand) => {
           let typed_first_operand = type_expression(*first_operand)?; 
           let typed_second_operand = type_expression(*second_operand)?;
            Operation::Binary(typed_first_operand, operator, typed_second_operand)
         }
    })
}
