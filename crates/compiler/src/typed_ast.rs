use anyhow::{bail, Result};
use melior::{dialect::llvm, ir::r#type::IntegerType, Context};
use std::collections::{BTreeMap, HashMap};

use crate::parser::{
    self, AccessModes, Ast, FunctionKeyword, Operator, TSExpression, TSIdentifier, TSType, TSValue,
};

#[derive(Debug, Clone)]
pub enum Type {
    Struct(StructType),
    Function(Vec<FunctionKeyword>, Vec<FunctionArg>, Box<Type>),
    Named(TSIdentifier),
    String,
    Unknown,
    Integer,
    UnsignedInteger,
    Boolean,
    Pointer,
    Unit,
    Array(Box<Type>, usize),
}

impl Type {
    pub fn as_mlir_type<'c>(
        &self,
        context: &'c Context,
        types: &BTreeMap<TSIdentifier, Type>,
    ) -> melior::ir::Type<'c> {
        match self {
            Type::Pointer => llvm::r#type::opaque_pointer(context),
            Type::String => llvm::r#type::opaque_pointer(context),
            Type::Integer => IntegerType::new(context, 32).into(),
            Type::Unit => llvm::r#type::void(context),
            Type::Struct(StructType {
                identifier: _,
                fields,
            }) => llvm::r#type::r#struct(
                context,
                fields
                    .iter()
                    .map(|f| f.field_type.as_mlir_type(context, types))
                    .collect::<Vec<melior::ir::Type>>()
                    .as_slice(),
                true,
            ),
            Type::Named(id) => types
                .get(id)
                .unwrap_or_else(|| panic!("failed to find named type {}", id.0.clone()))
                .as_mlir_type(context, types),
            Type::Array(item_type, length) => {
                llvm::r#type::array(item_type.as_mlir_type(context, types), *length as u32)
            }
            Type::UnsignedInteger => IntegerType::unsigned(context, 8).into(),
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

impl From<TSType> for Type {
    fn from(ty: TSType) -> Self {
        match ty {
            TSType::StringLiteral => Self::String,
            TSType::SignedInteger => Self::Integer,
            TSType::UnsignedInteger => Self::UnsignedInteger,
            TSType::Array(ty, length) => Self::Array(Type::from(*ty).into(), length),
            TSType::Named(name) => Self::Named(name),
            TSType::Pointer => Self::Pointer,
            _ => todo!(),
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
    pub block: Block,
}

#[derive(Debug, Clone)]
pub struct Assign {
    pub id: TSIdentifier,
    pub expression: Box<TypedExpression>,
}

#[derive(Debug, Clone)]
pub struct Return {
    pub expression: Option<Box<TypedExpression>>,
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
    Return(Return),
    Array(Array),
    ArrayLookup(ArrayLookup),
}

#[derive(Debug, Clone)]
pub struct ArrayLookup {
    pub array_identifier: TSIdentifier,
    pub index_expression: Box<TypedExpression>,
}

#[derive(Debug, Clone)]
pub struct Array {
    pub item_type: Type,
    pub items: Vec<TypedExpression>,
}

impl TypedExpression {
    pub fn r#type(&self, types: &BTreeMap<TSIdentifier, Type>) -> Result<Type> {
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
            Self::Return(Return { expression }) => {
               Ok(if let Some(expression) = expression {
                   expression.r#type(types)? 
                } else {
                    Type::Unit
                })
            }
            Self::Array(Array { item_type, items }) => Ok(Type::Array(Box::new(item_type.clone()), items.len() )),
            Self::ArrayLookup(ArrayLookup { array_identifier, ..}) => {
               if let Some(Type::Array(item_type, .. )) = types.get(array_identifier) {
                    Ok(*item_type.clone())
                } else {
                    bail!("failed to find array type for array lookup of {}", array_identifier.0)
                }
            }
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
    pub statements: Vec<TypedAst>,
}

#[derive(Debug, Clone)]
pub enum Decl {
    Struct(StructType),
    Function {
        keywords: Vec<FunctionKeyword>,
        id: TSIdentifier,
        arguments: Vec<FunctionArg>,
        body: Option<Vec<TypedAst>>,
        return_type: Type,
    },
}

#[derive(Debug, Clone)]
pub struct StructType {
    pub identifier: TSIdentifier,
    pub fields: Vec<StructField>,
}

#[derive(Debug, Clone)]
pub struct StructField {
    pub field_name: TSIdentifier,
    pub field_type: Type,
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
    pub access_mode: AccessModes,
}

#[derive(Debug, Clone)]
pub struct TypedProgram {
    pub types: BTreeMap<TSIdentifier, Type>,
    pub ast: Vec<TypedAst>,
    pub variable_types: HashMap<TSIdentifier, Type>,
}

#[derive(Debug, Clone)]
pub enum Operation {
    Binary(TypedExpression, Operator, TypedExpression),
}

fn ast_to_typed(node: parser::TypedAst) -> Result<TypedAst> {
    Ok(match node {
        parser::TypedAst::Expression(exp) => TypedAst::Expression(type_expression(exp)?),
        parser::TypedAst::StructType(parser::TSStructType { identifier, fields }) => {
            TypedAst::Decl(Decl::Struct(StructType {
                identifier,
                fields: fields
                    .into_iter()
                    .map(|f| StructField {
                        field_name: f.field_name,
                        field_type: f.field_type.into(),
                    })
                    .collect(),
            }))
        }
        parser::TypedAst::Assignment(var_id, init_expression) => {
            let expression = type_expression(init_expression)?;

            TypedAst::Assignment(Assignment {
                id: var_id,
                expression,
                typed_annotation: None,
            })
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
                    r#type: f.r#type.unwrap().into(),
                    access_mode: f.access_mode,
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
    Ok(IfStatement {
        condition: type_expression(*if_statement.condition)?.into(),
        then_block: type_block(if_statement.then_block)?,
        else_block: if let Some(block) = if_statement.else_block {
            Some(type_block(block)?)
        } else {
            None
        },
    })
}

fn type_block(block: parser::TSBlock) -> Result<Block> {
    let typed_statements = block
        .statements
        .into_iter()
        .map(ast_to_typed)
        .collect::<Result<Vec<TypedAst>>>()?;

    Ok(Block {
        statements: typed_statements,
    })
}

pub fn type_ast(ast: Ast) -> Result<TypedProgram> {
    let typed_ast = ast
        .0
        .into_iter()
        .map(ast_to_typed)
        .collect::<Result<Vec<TypedAst>>>()?;

    let mut types: BTreeMap<TSIdentifier, Type> = BTreeMap::new();
    let mut variable_types: HashMap<TSIdentifier, Type> = HashMap::new();
    let mut nodes = typed_ast.clone();

    loop {
        let Some(node) = nodes.pop() else {
            break;
        };

        if let TypedAst::Decl(decl) = node {
            match decl {
                Decl::Struct(t) => {
                    types.insert(t.identifier.clone(), Type::Struct(t));
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
    }

    let mut nodes = typed_ast.clone();
    loop {
        let Some(node) = nodes.pop() else {
            break;
        };

        match node {
            TypedAst::Decl(decl) => {
                if let Decl::Function {
                    body, arguments, ..
                } = decl
                {
                    if let Some(mut body) = body {
                        nodes.append(&mut body);
                    }

                    for arg in arguments {
                        let ty = if let Type::Named(ty_id) = arg.r#type {
                            types
                                .get(&ty_id)
                                .unwrap_or_else(|| panic!("failed to find {}", ty_id.0))
                                .clone()
                        } else {
                            arg.r#type
                        };
                        variable_types.insert(arg.name, ty);
                    }
                };
            }

            TypedAst::Assignment(Assignment {
                id,
                expression,
                typed_annotation,
            }) => {
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
                .map(type_expression)
                .collect::<Result<Vec<TypedExpression>>>()?,
        ),
        TSExpression::Value(val) => match val.clone() {
            TSValue::String(_) => TypedExpression::Value(val, Type::String),
            TSValue::Variable(_) => TypedExpression::Value(val, Type::Unknown),
            TSValue::Integer(_) => TypedExpression::Value(val, Type::Integer),
            TSValue::Boolean(_) => TypedExpression::Value(val, Type::Boolean),
            _ => todo!("missing type expression for {:?}", val),
        },
        TSExpression::Call(function_id, arguments) => TypedExpression::Call(
            function_id,
            arguments
                .into_iter()
                .map(type_expression)
                .collect::<Result<Vec<TypedExpression>>>()?,
        ),
        TSExpression::StructFieldRef(struct_id, field_id) => {
            TypedExpression::StructFieldRef(struct_id, field_id)
        }

        TSExpression::Operation(operation) => {
            TypedExpression::Operation(typed_operator(operation)?.into())
        }
        TSExpression::If(if_statement) => TypedExpression::If(type_if(if_statement)?),
        TSExpression::While(r#while) => TypedExpression::While(type_while(r#while)?),
        TSExpression::Assign(assign) => TypedExpression::Assign(type_assign(assign)?),
        TSExpression::Return(r#return) => TypedExpression::Return(type_return(r#return)?),
        TSExpression::Array(array) => TypedExpression::Array(type_array(array)?),
        TSExpression::ArrayLookup(array_lookup) => {
            TypedExpression::ArrayLookup(type_array_lookup(array_lookup)?)
        }
    })
}

fn type_array_lookup(array_lookup: parser::ArrayLookup) -> Result<ArrayLookup> {
    let index = type_expression(*array_lookup.index_expression)?;
    Ok(ArrayLookup {
        array_identifier: array_lookup.array_identifier,
        index_expression: Box::new(index),
    })
}

fn type_array(array: parser::Array) -> Result<Array> {
    let items = array
        .items
        .into_iter()
        .map(type_expression)
        .collect::<Result<Vec<TypedExpression>>>()?;
    let item_type = items[0].r#type(&BTreeMap::new())?;

    Ok(Array { item_type, items })
}

fn type_return(r#return: parser::Return) -> Result<Return> {
    let return_expression = if let Some(expression) = r#return.expression {
        Some(type_expression(*expression)?.into())
    } else {
        None
    };

    Ok(Return {
        expression: return_expression,
    })
}

fn type_assign(assign: parser::Assign) -> Result<Assign> {
    Ok(Assign {
        id: assign.id,
        expression: type_expression(*assign.expression)?.into(),
    })
}

fn type_while(r#while: parser::While) -> Result<While> {
    let condition = type_expression(*r#while.condition)?;
    let block = type_block(r#while.block)?;

    Ok(While {
        condition: condition.into(),
        block,
    })
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
