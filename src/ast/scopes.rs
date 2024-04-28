use crate::ast::NodeID;
use crate::ast::ScopeID;
use std::collections::HashMap;

use super::identifiers::DeclarationID;
use super::identifiers::StatementID;
use super::Ast;
use super::NodeDatabase;

#[derive(Debug, Clone)]
pub struct Scope {
    pub nodes: Vec<NodeID>,
    pub parent_scope: Option<ScopeID>,
    pub associated_node: Option<NodeID>,
}

pub fn build_program_scopes(ast: &Ast, db: &NodeDatabase) -> HashMap<ScopeID, Scope> {
    let mut scopes: HashMap<ScopeID, Scope> = HashMap::new();

    let root_scope_id = db.new_id::<ScopeID>();
    let root_scope = Scope {
        nodes: Vec::new(),
        parent_scope: None,
        associated_node: None,
    };

    scopes.insert(root_scope_id, root_scope);
    let mut current_scope_id = root_scope_id;

    let mut que: Vec<NodeID> = ast
        .modules
        .clone()
        .into_iter()
        .map(|module_id| module_id.into())
        .collect();

    let node_relationships = ast.get_node_relationships(db);
    let mut scope_stack = vec![current_scope_id];

    while let Some(node_id) = que.pop() {
        scopes
            .get_mut(&current_scope_id)
            .unwrap()
            .nodes
            .push(node_id);

        match node_id {
            NodeID::Declaration(DeclarationID::FunctionDeclaration(_))
            | NodeID::Statement(StatementID::Declaration(DeclarationID::FunctionDeclaration(_)))
            | NodeID::Block(_) => {
                let new_scope = Scope {
                    nodes: Vec::new(),
                    parent_scope: Some(current_scope_id),
                    associated_node: Some(node_id),
                };

                let new_scope_id = db.new_id::<ScopeID>();
                scopes.insert(new_scope_id, new_scope);

                let current_scope = scopes.get(&current_scope_id).unwrap();
                while current_scope.associated_node.is_some()
                    && !node_relationships
                        .get(&current_scope.associated_node.unwrap())
                        .unwrap_or(&Vec::new())
                        .contains(&node_id)
                {
                    scope_stack.pop();
                }

                current_scope_id = new_scope_id;
                scope_stack.push(current_scope_id);

                for &child in node_relationships.get(&node_id).unwrap_or(&Vec::new()) {
                    que.push(child);
                }
            }
            _ => (),
        }
    }

    scopes
}
