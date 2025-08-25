use std::{collections::HashMap, fmt::Display};

use anyhow::{bail, Result};
use melior::{dialect::llvm, ir::r#type::IntegerType, Context};

use super::{
    declarations::ModuleDeclaration,
    identifiers::{BlockID, ExpressionID, StatementID},
    Scope,
    NodeDatabase
};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Default)]
pub struct Identifier(pub String);

impl Identifier {
    pub fn new(name: String) -> Self {
        Self(name)
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub enum Type {
    String,
    StringLiteral,
    SignedInteger,
    UnsignedInteger,
    Boolean,
    Function,
    Named(Identifier),
    Array(Box<Type>, usize), // TODO: get rid of this Box
    Pointer,
    Unit,
}

// TODO: this should really happen in the types module.
impl Type {
    pub fn as_mlir_type<'c, 'a>(&self, context: &'c Context, types: &HashMap<Identifier, Type>) -> melior::ir::Type<'a> where 'c: 'a {
        match self {
            Type::Pointer => llvm::r#type::opaque_pointer(context),
            Type::String => llvm::r#type::opaque_pointer(context),
            Type::SignedInteger => IntegerType::new(context, 32).into(),
            Type::Unit => llvm::r#type::void(context),
            Type::StringLiteral => llvm::r#type::opaque_pointer(context),
            _ => todo!("unimplemented type to mlir type {:?}", self),
        }
    }
}

#[derive(Debug, Clone)]
pub struct StructDeclaration {
    pub identifier: Identifier,
    pub fields: Vec<StructField>,
}

#[derive(Debug, Clone)]
pub struct StructField {
    pub identifier: Identifier,
    pub r#type: Type,
}

#[derive(Debug, Clone, PartialEq, PartialOrd, Eq)]
pub struct FunctionDeclaration {
    pub keywords: Vec<FunctionKeyword>,
    pub identifier: Identifier,
    pub arguments: Vec<FunctionArg>,
    pub body: Option<BlockID>,
    pub return_type: Option<Type>,
}

impl FunctionDeclaration {
    pub fn is_external(&self) -> bool {
        self.keywords.contains(&FunctionKeyword::LlvmExtern)
    }

    pub fn get_return_type(&self) -> Type {
        self.return_type.clone().unwrap_or(Type::Unit)
    }

    pub fn argument_types(&self) -> impl Iterator<Item = &Type> {
        self.arguments.iter().map(|argument| argument.r#type.as_ref().expect(&format!("expected a parameter type in function {:?}", self.identifier)))
    }
    
    pub fn parameter_access_modes(&self) -> impl Iterator<Item = AccessModes> + '_ {
        self.arguments.iter().map(|argument| argument.access_mode.clone())
    }
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

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct FunctionArg {
    pub name: Identifier,
    pub r#type: Option<Type>,
    pub access_mode: AccessModes,
}

#[derive(Debug, Clone, Default, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum AccessModes {
    #[default]
    Let,
    Owned,
    Inout,
}

impl Display for AccessModes {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Let => f.write_str("let")?,
            Self::Owned => f.write_str("owned")?,
            Self::Inout => f.write_str("inout")?,
        }

        Ok(())
    }
}

#[derive(Debug, Clone)]
pub struct Block {
    pub statements: Vec<StatementID>,
}

impl Block {
    pub fn new(statements: Vec<StatementID>) -> Self {
        Self { statements }
    }
}

#[derive(Debug, Clone)]
pub enum Node {
    Statement(Statement),
    Scope(Scope),
}

#[derive(Debug, Clone)]
pub enum Statement {
    Expression(Expression),
    Declaration(Declaration),
}

#[derive(Debug, Clone)]
pub enum Declaration {
    Function(FunctionDeclaration),
    Struct(StructDeclaration),
    Module(ModuleDeclaration),
}

#[derive(Debug, Clone)]
pub enum Expression {
    Value(Value),
    Call(Call),
    Struct(StructInit),
    StructFieldRef(StructFieldPath),
    Operation(Operation),
    If(IfStatement),
    Ifelse(IfElseStatement),
    While(While),
    Assign(Assign),
    Assignment(Assignment),
    Return(Return),
    Array(Array),
    ArrayLookup(ArrayLookup),
    Block(BlockID),
}

impl Expression {
    // TODO: Ownership indicators are not present here
    pub fn to_debug_string(&self, db: &NodeDatabase) -> Result<String> {
        Ok(match self {
            Expression::Value(value) => {
                value.to_debug_string()
            }
            Expression::Assignment(assignment) => {
               format!("{} = {} ",  assignment.id.0, db.expressions.get(&assignment.expression).unwrap().to_debug_string(db)?) 
            }
            Expression::Return(ret) => {
                if let Some(return_expression) = ret.expression {
                    format!("return {} ",  db.expressions.get(&return_expression).unwrap().to_debug_string(db)?) 
                } else {
                    "return".to_string()
                }
            }
            Expression::Call(call) => {
                let arguments: Vec<String> = call.arguments.iter().map(|id|  db.expressions.get(id).unwrap().to_debug_string(db).unwrap()).collect();
                format!("call {}({:?})", call.function_id.0, arguments)
            }
            Expression::Operation(operation) => {
               operation.to_debug_string(db)? 
            }
            Expression::Array(array) => {
                let arguments: Vec<String> = array.items.iter().map(|id|  db.expressions.get(id).unwrap().to_debug_string(db).unwrap()).collect();
                format!("array[{:?}]", arguments)

            }
            Expression::ArrayLookup(array_lookup) => {
                let index_debug_string = db.expressions.get(&array_lookup.index_expression).unwrap().to_debug_string(db)?;
                format!("arraylookup({}, {})", array_lookup.array_identifier.0, index_debug_string) 
            }
            Expression::Ifelse(if_else_statement) => {
                let debug_string = "if_else_start";
                debug_string.to_string()
            }
            e => todo!("implement debug string for expression {e:?}")
        })
    }
}

// TODO: Replace string identifiers with something int based.
// TODO: support nested paths
#[derive(Debug, Clone)]
pub struct StructFieldPath {
    pub struct_indentifier: Identifier,
    pub field_identifier: Identifier,
}

#[derive(Debug, Clone)]
pub struct StructInit {
    pub struct_id: Identifier,
    pub field_values: Vec<ExpressionID>,
}

#[derive(Debug, Clone)]
pub struct Call {
    pub function_id: Identifier,
    pub arguments: Vec<ExpressionID>,
}

#[derive(Debug, Clone)]
pub struct ArrayLookup {
    pub array_identifier: Identifier,
    pub index_expression: ExpressionID,
}

#[derive(Debug, Clone)]
pub struct IfStatement {
    pub condition: ExpressionID,
    pub then_block: BlockID,
}

#[derive(Debug, Clone)]
pub struct IfElseStatement {
    pub condition: ExpressionID,
    pub then_block: BlockID,
    pub else_block: BlockID,
}
#[derive(Debug, Clone)]
pub struct Array {
    pub items: Vec<ExpressionID>,
}

#[derive(Debug, Clone)]
pub struct Return {
    pub expression: Option<ExpressionID>,
}

#[derive(Debug, Clone)]
pub struct Assign {
    pub id: Identifier,
    pub expression: ExpressionID,
}

#[derive(Debug, Clone)]
pub struct Assignment {
    pub id: Identifier,
    pub expression: ExpressionID,
}


#[derive(Debug, Clone)]
pub struct While {
    pub condition: BlockID,
    pub body: BlockID,
}

#[derive(Debug, Clone)]
pub struct StructType {
    pub identifier: Identifier,
    pub fields: Vec<StructField>,
}

#[derive(Debug, Clone)]
pub enum Operation {
    Binary(ExpressionID, Operator, ExpressionID),
}

impl Operation {
    pub fn to_debug_string(&self, db: &NodeDatabase) -> Result<String> {
        match self {
            Self::Binary(lhs, operator, rhs) => {
                let lhs_debug_string = db.expressions.get(lhs).unwrap().to_debug_string(db)?;
                let rhs_debug_string = db.expressions.get(rhs).unwrap().to_debug_string(db)?;
                let operator_debug_string = operator.to_debug_string();
                Ok(format!("Operation({lhs_debug_string} {operator_debug_string} {rhs_debug_string})"))
            }
        }
    }
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

impl Operator {
    pub fn to_debug_string(&self) -> String {
        match self {
            Self::Addition => String::from("+"),
            Self::Subtraction => String::from("-"),
            Self::Multiplication => String::from("*"),
            Self::Division => String::from("/"),
            _ => todo!("implement debug string for operation {:?}", self)
        }
    }
}

#[derive(Debug, Clone)]
pub enum Value {
    String(String),
    Variable(Identifier),
    Integer(Integer),
    Boolean(bool),
}

impl Value {
    pub fn to_debug_string(&self) -> String {
        match self {
            Value::String(text) => format!("\"{text}\""),
            Value::Variable(id) => format!("Variable({})", id.0),
            Value::Integer(value) => format!("Int({})", value.value),
            Value::Boolean(value) => format!("Boolean({})", value),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Integer {
    pub(crate) signed: bool,
    pub(crate) size: usize,
    pub(crate) value: isize,
}
