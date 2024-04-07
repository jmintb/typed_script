use std::collections::HashMap;

use crate::ast::identifiers::{ExpressionID, NodeID, ScopeID, TypeID};
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

    let mut walker = |db: &NodeDatabase,
                      node_id: NodeID,
                      parent_node_id: Option<NodeID>,
                      output: &mut WalkerContext| { Ok(()) };

    ast.traverse(db, &mut walker, &mut walker_context);

    walker_context.0
}
