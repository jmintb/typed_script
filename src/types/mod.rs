use std::collections::HashMap;

use crate::ast::nodes::{
     Expression,  FunctionKeyword, Identifier, StructDeclaration, Value, Assignment,
};
use crate::ast::scopes::Scope;
use crate::ast::{Ast, NodeDatabase};
use crate::ast::identifiers::{
    DeclarationID, ExpressionID, FunctionDeclarationID, NodeID, ScopeID, StatementID,
};
use crate::identifiers::{IDGenerator, ID};
use crate::ast::nodes::AccessModes;

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

#[derive(Debug, Clone, Hash, Eq, PartialEq)]
pub enum TypeID {
    Struct(StructTypeID),
    Function(FunctionTypeID),
    Named(NamedTypeID),
    Array(ArrayTypeID),
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

#[derive(Debug, Clone)]
pub struct FunctionType {
    pub key_words: Vec<FunctionKeyword>,
    pub return_type: Option<Type>,
    pub arguments: Vec<FunctionArgumentType>,
}

#[derive(Debug, Clone)]
pub struct FunctionArgumentType {
    pub name: Identifier,
    pub r#type: Type,
    pub access_mode: AccessModes,
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
    pub struct_types: HashMap<StructTypeID, StructDeclaration>,
    pub function_types: HashMap<FunctionTypeID, FunctionType>,
    pub function_declaration_types: HashMap<FunctionDeclarationID, FunctionTypeID>,
    id_generator: IDGenerator,
    pub ids: HashMap<TypeID, (Identifier, ScopeID)>,
}

impl TypeDB {
    fn new() -> Self {
        Self {
            struct_types: HashMap::new(),
            id_generator: IDGenerator::default(),
            function_declaration_types: HashMap::new(),
            function_types: HashMap::new(),
            ids: HashMap::new(),
        }
    }

    fn new_id<T: From<ID> + Into<TypeID> + Copy>(&mut self) -> T {
        self.id_generator.new_id::<T>()
    }

    fn new_type_id_for_identifier<T: From<ID> + Into<TypeID> + Copy>(
        &mut self,
        name: Identifier,
        scope_id: ScopeID,
    ) -> T {
        let id = self.new_id::<T>();
        self.ids.insert(id.into(), (name.clone(), scope_id));
        id
    }

    fn insert_struct_type(
        &mut self,
        struct_type: StructDeclaration,
        scope_id: ScopeID,
    ) -> StructTypeID {
        let id = self.new_type_id_for_identifier(struct_type.identifier.clone(), scope_id);
        self.struct_types.insert(id, struct_type);
        id
    }
}

pub struct Function {
    key_words: Vec<FunctionKeyword>,
    arguments: Vec<TypeID>,
    return_type: TypeID,
}

pub struct TypedProgram {
    pub ast: Ast,
    pub db: NodeDatabase,
    pub types: TypeDB,
    pub type_assignments: HashMap<ExpressionID, Type>,
}

pub fn resolve_types(
    ast: &Ast,
    db: &NodeDatabase,
    scopes: &HashMap<ScopeID, Scope>,
    root_scope: ScopeID,
) -> (HashMap<ExpressionID, Type>, TypeDB) {
    let mut type_db = TypeDB::new();
    let mut types = HashMap::new();

    let mut gather_types = |db: &NodeDatabase,
                            node_id: NodeID,
                            parent_node_id: Option<NodeID>,
                            output: &mut TypeDB| {
        match node_id {
            NodeID::Declaration(DeclarationID::StructDeclaration(ref id)) => {
                let struct_decl = db.struct_declarations.get(id).unwrap();

                output.insert_struct_type(struct_decl.clone(), ScopeID(0));
            }
            _ => (),
        }
        Ok(())
    };

    ast.traverse(db, &mut gather_types, &mut type_db);

    type WalkerContext = (HashMap<ExpressionID, Type>, ScopeID);
    // let mut walker_context: WalkerContext = (types, root_scope);

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

        // let return_type = function_declaration
        //     .return_type
        //     .map(|return_type| match return_type {
        //         nodes::Type::String => Type::String,
        //         _ => todo!("Add type conversion"),
        //     });

        // let function_type = FunctionType {
        //     key_words: function_declaration.keywords,
        //     return_type,
        //     arguments: function_declaration.arguments,
        // };

        // let

        let Some(function_body_id) = function_declaration.body else {
            break;
        };

        let function_body = db.blocks.get(&function_body_id).unwrap();

        for statement in function_body.statements.iter() {
            match statement {
                StatementID::Expression(id) => {
                    let expression = db.expressions.get(&id).unwrap();
                    let expression_type = match expression {
                        Expression::Value(value) => match value {
                            Value::String(..) => Type::String,
                            _ => todo!(),
                        },
                        Expression::Assignment(Assignment {
                            id, expression
                        }) =>  Type::Unit, 
                        _ => Type::Unit,

                        _ => todo!("typing not implemented for {:?}", expression),
                    };
                    types.insert(*id, expression_type);
                }
                _ => todo!(),
            }
        }

        // TODO: add expression types
    }

    (types, type_db)
}
