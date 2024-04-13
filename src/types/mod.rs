use std::collections::HashMap;

use crate::ast::identifiers::{ExpressionID, FunctionDeclarationID, NodeID, ScopeID};
use crate::ast::nodes::Identifier;
use crate::ast::{Ast, NodeDatabase, Scope};
use crate::identifiers::ID;
use crate::parser::FunctionKeyword;

pub struct TypedProgram {
    ast: Ast,
    scopes: HashMap<ScopeID, Vec<ScopeID>>,
    types: HashMap<ExpressionID, TypeID>,
}

#[derive(Debug, Clone)]
pub enum Type {
    Struct(StructTypeID),
    Function(FunctionTypeID),
    Named(NamedTypeID),
    String,
    Unknown,
    Integer(SignedIntegerType),
    UnsignedInteger(UnsignedIntegerType),
    Boolean,
    Pointer,
    Unit,
    Array(ArrayTypeID),
}

#[derive(Debug, Clone)]
pub struct SignedIntegerType(usize);

#[derive(Debug, Clone)]
pub struct UnsignedIntegerType(usize);

#[derive(Debug, Clone)]
pub enum TypeID {
    Struct(StructTypeID),
    Function(FunctionTypeID),
    Named(NamedTypeID),
    Array(ArrayTypeID)
}

#[derive(Debug, Clone)]
pub struct StructType {
    pub identifier: Identifier,
    pub fields: Vec<StructField>,
}

#[derive(Debug, Clone)]
pub struct StructField {
    pub field_name: Identifier,
    pub field_type: TypeID,
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Copy, Clone, Hash, Debug)]
pub struct StructTypeID(ID);

impl From<ID> for StructTypeID {
    fn from(value: ID) -> Self {
        Self(value)
    }
}

impl From<StructTypeID> for TypeID {
    fn from(value: StructTypeID) -> Self {
        Self::Struct(value)
    }
}



#[derive(PartialEq, Eq, PartialOrd, Ord, Copy, Clone, Hash, Debug)]
pub struct FunctionTypeID(ID);

impl From<ID> for FunctionTypeID {
    fn from(value: ID) -> Self {
        Self(value)
    }
}

impl From<FunctionTypeID> for TypeID {
    fn from(value: FunctionTypeID) -> Self {
        Self::Function(value)

    }
}


#[derive(PartialEq, Eq, PartialOrd, Ord, Copy, Clone, Hash, Debug)]
pub struct NamedTypeID(ID);

impl From<ID> for NamedTypeID {
    fn from(value: ID) -> Self {
        Self(value)
    }
}

impl From<NamedTypeID> for TypeID {
    fn from(value: NamedTypeID) -> Self {
        Self::Named(value)
    }
}


#[derive(PartialEq, Eq, PartialOrd, Ord, Copy, Clone, Hash, Debug)]
pub struct ArrayTypeID(ID);

impl From<ID> for ArrayTypeID {
    fn from(value: ID) -> Self {
        Self(value)
    }
}

impl From<ArrayTypeID> for TypeID {
    fn from(value: ArrayTypeID) -> Self {
        Self::Array(value)
    }
}

#[derive(Debug, Clone)]
pub struct TypeDB {
    struct_types: HashMap<StructTypeID, StructType>    
}
impl TypeDB {
    fn new() -> Self {
        Self {
            struct_types: HashMap::new()
        }
    }
}

pub struct Function {
    key_words: Vec<FunctionKeyword>,
    arguments: Vec<TypeID>,
    return_type: TypeID 
}

pub fn resolve_types(
    ast: Ast,
    db: &NodeDatabase,
    scopes: &HashMap<ScopeID, Vec<ScopeID>>,
    root_scope: ScopeID,
) -> HashMap<ExpressionID, TypeID> {
    let mut type_db = TypeDB::new();
    let mut types = HashMap::new();
    type WalkerContext = (HashMap<ExpressionID, TypeID>, ScopeID);
    let mut walker_context: WalkerContext = (types, root_scope);

    // TODO; create a traverser which incldues the current scope.
    let function_declarations: Vec<FunctionDeclarationID> = db
        .module_declarations
        .iter()
        .map(|(_, module_declaration)| module_declaration.function_declarations.clone())
        .flatten()
        .collect();

    for function_declaration_id in function_declarations {
        let function_declaration = db
            .function_declarations
            .get(&function_declaration_id)
            .unwrap();

        // TODO: add function type

        let function_type = FunctionType

        let Some(function_body) = function_declaration.body else {
            break;
        };

        // TODO: add expression types
    }

    walker_context.0
}
