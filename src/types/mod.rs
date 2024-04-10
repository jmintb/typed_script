use std::collections::HashMap;

use crate::ast::identifiers::{ExpressionID, FunctionDeclarationID, NodeID, ScopeID, TypeID};
use crate::ast::{Ast, NodeDatabase, Scope};

pub struct TypedProgram {
    ast: Ast,
    scopes: HashMap<ScopeID, Vec<ScopeID>>,
    types: HashMap<ExpressionID, TypeID>,
}

pub fn resolve_types(
    ast: Ast,
    db: &NodeDatabase,
    scopes: &HashMap<ScopeID, Vec<ScopeID>>,
    root_scope: ScopeID,
) -> HashMap<ExpressionID, TypeID> {
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

        let Some(function_body) = function_declaration.body else {
            break;
        };

        // TODO: add expression types
    }

    walker_context.0
}
