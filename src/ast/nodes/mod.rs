use std::{collections::{BTreeMap, HashMap}, fmt::Display};

use anyhow::bail;
use melior::{dialect::llvm, ir::r#type::IntegerType, Context};

use super::{
    declarations::ModuleDeclaration,
    identifiers::{BlockID, ExpressionID, FunctionDeclarationID, StatementID},
    Scope,
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
    pub fn as_mlir_type<'c>(&self, context: &'c Context, types: &HashMap<Identifier, Type>) -> melior::ir::Type<'c> {
        match self {
            Type::Pointer => llvm::r#type::opaque_pointer(context),
            Type::String => llvm::r#type::opaque_pointer(context),
            Type::SignedInteger => IntegerType::new(context, 32).into(),
            Type::Unit => llvm::r#type::void(context),
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
    pub condition: ExpressionID,
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
pub enum Value {
    String(String),
    Variable(Identifier),
    Number,
    Integer(Integer),
    Boolean(bool),
}

#[derive(Debug, Clone)]
pub struct Integer {
    pub(crate) signed: bool,
    pub(crate) size: usize,
    pub(crate) value: isize,
}
