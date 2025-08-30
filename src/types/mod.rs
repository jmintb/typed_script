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
use crate::ast::nodes;
use tracing::debug;
use std::marker::PhantomData;

#[derive(Debug, Clone, Copy, Default)]
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
    #[default]
    Unit,
    Array(ArrayTypeID),
}

impl Type {
    fn from_ast_node(node: &nodes::Type) -> Self {
        match node {
                 crate::ast::nodes::Type::String => Self::String,
                 crate::ast::nodes::Type::StringLiteral => Self::String,
                 crate::ast::nodes::Type::Pointer => Self::Pointer,
                 crate::ast::nodes::Type::SignedInteger => Self::Integer(SignedIntegerType(32)),
                 crate::ast::nodes::Type::Unit => Self::Unit,
                 _ => todo!("Add type conversion {:?}", node),
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct SignedIntegerType(pub usize);

#[derive(Debug, Clone, Copy)]
pub struct UnsignedIntegerType(pub usize);

#[derive(Debug, Clone, Hash, Eq, PartialEq)]
pub enum TypeID {
    Struct(StructTypeID),
    Function(FunctionTypeID),
    Named(NamedTypeID),
    Array(ArrayTypeID),
}

#[derive(Debug, Clone, Copy, Default)]
pub struct ArrayType {
    pub element_type: Type,
    pub length: usize
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
    pub return_type: Type,
    pub parameter_types: Vec<Type>,
    pub parameter_access_modes: Vec<AccessModes>,
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

#[derive(PartialEq, Eq, PartialOrd, Ord, Copy, Clone, Hash, Debug, Default)]
pub struct ArrayTypeID(ID);


impl From<ID> for ArrayTypeID {
    fn from(value: ID) -> Self {
        Self(value)
    }
}

impl Into<usize> for ArrayTypeID {
    fn into(self) -> usize {
        self.0
    }
}

impl From<ArrayTypeID> for TypeID {
    fn from(value: ArrayTypeID) -> Self {
        Self::Array(value)
    }
}

#[derive(Clone, Debug, Default)]
pub struct FlatEntityStore<T, K: From<usize>> {
    entities: Vec<T>,
    // This is only to force a specific type is used as the IDs in a store. It stores no data at runtime.
    id_type_marker: PhantomData<K>
}

impl<T, K: From<usize> + Into<usize>> FlatEntityStore<T, K>  {
    pub fn insert(&mut self, entity: T) -> K {
        let next_id = self.entities.len();
        self.entities.push(entity);
        K::from(next_id)
    }

    pub fn get(&self, id: K) -> Option<&T> {
        self.entities.get(id.into())
    }

    fn new() -> Self {
        Self {
            entities: Vec::new(),
            id_type_marker: PhantomData{}
        }
    }
}


#[derive(Debug, Clone)]
pub struct TypeDB {
    pub struct_types: HashMap<StructTypeID, StructDeclaration>,
    pub function_types: HashMap<FunctionTypeID, FunctionType>,
    pub function_declaration_types: HashMap<FunctionDeclarationID, FunctionTypeID>,
    id_generator: IDGenerator,
    pub ids: HashMap<TypeID, (Identifier, ScopeID)>, // TODO: get rid of identifier at this stage in the compiler.
    pub array_types: FlatEntityStore<ArrayType, ArrayTypeID>,
}

impl TypeDB {
    fn new() -> Self {
        Self {
            struct_types: HashMap::new(),
            id_generator: IDGenerator::default(),
            function_declaration_types: HashMap::new(),
            function_types: HashMap::new(),
            ids: HashMap::new(),
            array_types: FlatEntityStore::new(),
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

    fn insert_function_type(
        &mut self,
        function_declaration: FunctionDeclarationID,
        r#type: FunctionType,
        ) -> FunctionTypeID {
        let id = self.new_id::<FunctionTypeID>();
        self.function_types.insert(id, r#type);
        self.function_declaration_types.insert(function_declaration, id);
        id
    }
}

pub struct Function {
    key_words: Vec<FunctionKeyword>,
    arguments: Vec<TypeID>,
    return_type: TypeID,
}

// NEXT: fix types resolving enough to get function return types resolved.
// Maybe the get the API right atleast instead of hacking around. -> start inserting function types into TypeDB
pub fn resolve_types(
    ast: &Ast,
    db: &NodeDatabase,
    _scopes: &HashMap<ScopeID, Scope>,
    _root_scope: ScopeID,
) -> (HashMap<ExpressionID, Type>, TypeDB) {
    let mut type_db = TypeDB::new();
    let mut types = HashMap::new();

    let mut gather_type_declarations = |db: &NodeDatabase,
                            node_id: NodeID,
                            _parent_node_id: Option<NodeID>,
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

    ast.traverse(db, &mut gather_type_declarations, &mut type_db);

    type WalkerContext = (HashMap<ExpressionID, Type>, ScopeID);
    // let mut walker_context: WalkerContext = (types, root_scope);

    // TODO; create a traverser which incldues the current scope.
    let function_declarations: Vec<FunctionDeclarationID> = db
        .module_declarations
        .iter()
        .map(|(_, module_declaration)| module_declaration.function_declarations.clone())
        .flatten()
        .collect();

    for (id, expression) in db.expressions.iter() {
        match expression {
            Expression::Value(Value::String(_)) => {
                types.insert(*id, Type::String);
            }
            Expression::Value(Value::Integer(_)) => {
                types.insert(*id, Type::Integer(SignedIntegerType(32)));
            }
            _ => ()
        }
    }

    debug!("resolving types for functions {:?}", function_declarations);

    for function_declaration_id in function_declarations {
        let function_declaration = db
            .function_declarations
            .get(&function_declaration_id)
            .unwrap();


         let return_type = Type::from_ast_node(function_declaration
             .return_type
             .as_ref()
             .unwrap_or(&nodes::Type::Unit)
             );

         let parameter_types = function_declaration.argument_types().map(Type::from_ast_node).collect();
         let parameter_access_modes = function_declaration.parameter_access_modes().collect();


         let function_type = FunctionType {
             key_words: function_declaration.keywords.clone(),
             return_type: return_type,
             parameter_types: parameter_types,
             parameter_access_modes: parameter_access_modes,
         };

        let function_type_id = type_db.insert_function_type(function_declaration_id, function_type.clone());
         debug!("storing type {:?} {:?} for function declaration {:?} {:?}", function_type_id, function_type, function_declaration.identifier, function_declaration_id);

        let Some(function_body_id) = function_declaration.body else {
            continue;
        };

        let function_body = db.blocks.get(&function_body_id).unwrap();

        for statement in function_body.statements.iter() {
            match statement {
                StatementID::Expression(id) => {
                    let expression = db.expressions.get(&id).unwrap();
                    debug!("typing statement: {:?}", expression);
                    let expression_type = match expression {
                        Expression::Value(value) => match value {
                            Value::String(..) => Type::String,
                            _ => todo!(),
                        },
                        Expression::Assignment(Assignment {
                            id: _, expression: _
                        }) =>  Type::Unit, 
                        Expression::Array(_array) => {
                            //let array_type = ArrayType {length: array.items.len(), element_type:  //NEXT evaluate the experession type inside the array.};
                            todo!();
                        }


                        _ => Type::Unit
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
