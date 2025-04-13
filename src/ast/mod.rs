pub mod declarations;
pub mod identifiers;
pub mod nodes;
pub mod parser;
pub mod scopes;

use std::collections::{HashMap, VecDeque};
use anyhow::{Result, bail};
use tracing::debug;

use crate::{identifiers::{IDGenerator, ID}, parser::TSIdentifier};

use self::{
    declarations::ModuleDeclaration,
    identifiers::{BlockID, ExpressionID, ScopeID, StatementID},
    nodes::{
        Block, Declaration, Expression, FunctionDeclaration, Identifier, IfElseStatement,
        IfStatement, Node, Statement, StructDeclaration, While,
    },
};
use super::ast::identifiers::{
    DeclarationID, FunctionDeclarationID, ModuleDeclarationID, NodeID, StructDeclarationID,
};

type WalkerFn<Ctx> = dyn FnMut(&NodeDatabase, NodeID, Option<NodeID>, &mut Ctx) -> Result<()>;

#[derive(Debug, Clone)]
pub struct Scope {
    pub nodes: Vec<NodeID>,
    pub parent_scope: Option<ScopeID>,
    pub associated_node: Option<NodeID>,
}

#[derive(Debug, Clone)]
pub struct Ast {
    modules: Vec<ModuleDeclarationID>,
}

impl Ast {

    pub fn new() -> Self {
        Self {
            modules: Vec::new(),
        }
    }

    pub fn get_entry_function_id(&self, db: &NodeDatabase) -> Result<FunctionDeclarationID> {
        db.get_function_declaration_id_from_identifier(Identifier("main".to_string()))
    }

    pub fn get_node_relationships(&self, db: &NodeDatabase) -> HashMap<NodeID, Vec<NodeID>> {
        let mut output: (HashMap<NodeID, Vec<NodeID>>, Option<NodeID>) = (HashMap::new(), None);
        let mut walker =
            |db: &NodeDatabase,
             node_id: NodeID,
             parent_node_id: Option<NodeID>,
             output: &mut (HashMap<NodeID, Vec<NodeID>>, Option<NodeID>)| {
                if let Some(parent_id) = parent_node_id {
                    output
                        .0
                        .entry(parent_id)
                        .and_modify(|children| children.push(node_id))
                        .or_insert(vec![node_id]);
                }

                output.1 = parent_node_id;

                Ok(())
            };

        self.traverse(db, &mut walker, &mut output);

        output.0
    }

    // TODO: this kind of has too much detail now. Ideally we only want the structure of the tree.
    pub fn to_string(&self, db: &NodeDatabase) -> String {
        let mut output: (HashMap<NodeID, Vec<NodeID>>, Option<NodeID>) = (HashMap::new(), None);
        let mut walker =
            |db: &NodeDatabase,
             node_id: NodeID,
             parent_node_id: Option<NodeID>,
             output: &mut (HashMap<NodeID, Vec<NodeID>>, Option<NodeID>)| {
                if let Some(parent_id) = parent_node_id {
                    output
                        .0
                        .entry(parent_id)
                        .and_modify(|children| children.push(node_id))
                        .or_insert(vec![node_id]);
                }

                output.1 = parent_node_id;

                Ok(())
            };

        self.traverse(db, &mut walker, &mut output);

        let mut tree_rows = vec!["root".to_string()];

        let mut que: VecDeque<Vec<Vec<NodeID>>> = vec![self
            .modules
            .clone()
            .into_iter()
            .map(|module_id| vec![NodeID::from(module_id)])
            .collect()]
        .into();

        while let Some(parent_row) = que.pop_front() {
            let parent_names: Vec<Vec<String>> = parent_row
                .iter()
                .filter(|parent| !parent.is_empty())
                .map(|parent| {
                    parent
                        .iter().rev()
                        .map(|parent| {
                            match parent{
                                &NodeID::Declaration(DeclarationID::ModuleDeclarationID(id)) => format!("module_{}", id.0),
                                &NodeID::Block(BlockID(id)) => format!("block_{id}"),
                                &NodeID::Statement(StatementID::Expression(id)) => {
                                  db.expressions.get(&id).unwrap().to_debug_string(db).unwrap()
                                },
                                    &NodeID::Statement(StatementID::Declaration(_)) => {db.ids
                                .get(parent).map(|id| id.0.clone())
                                .unwrap_or("unnamed".to_string())
                                .clone()
                                    }
                                    &NodeID::Declaration(_) => {db.ids
                                .get(parent).map(|id| id.0.clone())
                                .unwrap_or("unnamed".to_string())
                                .clone()
                                    }
                                _ => todo!("format!({parent:?})")
                            }
                        })
                        .collect::<Vec<String>>()
                })
                .collect();

            debug!("parent names {:?}", parent_names);
            if !parent_names.is_empty() {
                tree_rows.push(format!("{:#?}", parent_names));
            }

            let next_row: Vec<Vec<NodeID>> = parent_row
                .iter()
                .flatten()
                .map(|parent| output.0.get(parent).unwrap_or(&Vec::new()).clone())
                .collect();

            if next_row.is_empty() {

                break;
            }

            que.push_back(next_row);
        }

        format!("{}", tree_rows.join(", "))
    }

    pub fn traverse<Ctx>(
        &self,
        db: &NodeDatabase,
        walker: &mut WalkerFn<Ctx>,
        walker_context: &mut Ctx,
    ) {
        let mut queue: VecDeque<(NodeID, Option<NodeID>)> = self
            .modules
            .iter()
            .map(|module_id| {
                (
                    NodeID::Declaration(DeclarationID::ModuleDeclarationID(*module_id)),
                    None,
                )
            })
            .collect();

        let mut process_block =
            |block_id: &BlockID,
             parent_id: Option<NodeID>,
             queue: &mut VecDeque<(NodeID, Option<NodeID>)>| {
                 let block = db.blocks.get(block_id).unwrap();
                for &statement in block.statements.iter() {
                    match statement {
                        StatementID::Declaration(decl) => todo!(),
                        StatementID::Expression(expression_id) => {
                            queue.push_front((expression_id.into(), parent_id));
                        }
                    }
                }
            };

        // TODO: this is not parralellised
        while let Some((next, parent)) = queue.pop_front() {
            match next {
                NodeID::Declaration(DeclarationID::ModuleDeclarationID(module_id)) => {
                    walker(db, module_id.into(), parent, walker_context).unwrap();
                    let module_declaration = db.module_declarations.get(&module_id).unwrap();
                    for &struct_declaration in module_declaration.struct_declarations.iter() {
                        queue.push_front((struct_declaration.into(), Some(module_id.into())));
                    }

                    for &function_declaration in module_declaration.function_declarations.iter() {
                        queue.push_front((function_declaration.into(), Some(module_id.into())));
                    }
                }

                NodeID::Declaration(DeclarationID::FunctionDeclaration(function_id)) => {
                    walker(db, function_id.into(), parent, walker_context).unwrap();
                    let function_declaration = db.function_declarations.get(&function_id).unwrap();

                    if let Some(body) = function_declaration.body {
                        queue.push_front((body.into(), Some(function_id.into())));
                    }
                }
                NodeID::Block(block_id) => {
                    walker(db, block_id.into(), parent, walker_context).unwrap();
                    process_block(&block_id, Some(block_id.into()), &mut queue);
                }

                // TODO: All expressions need to be "unpacked" and processed as they can contain blocks.

                // NEXT: Get If Ellse statement snapshots to include if/else blocks
                NodeID::Statement(StatementID::Expression(expression_id)) => {
                    let expression = db.expressions.get(&expression_id).unwrap();

                    match expression {
                        Expression::If(IfStatement {
                            condition, // TODO:conditions need  to be pressed by walker.
                            then_block,
                        }) => process_block(then_block, parent, &mut queue),
                        Expression::Ifelse(IfElseStatement {
                            condition,
                            then_block,
                            else_block,
                        }) => {
                            debug!("process ifelse statement, with parent {:?}", parent);
                            walker(db, expression_id.into(), parent, walker_context).unwrap();
                            queue.push_front(((*condition).into(), parent));
                            queue.push_front(((*then_block).into(), Some(expression_id.into())));
                            queue.push_front(((*else_block).into(), Some(expression_id.into())));
                        }
                        Expression::While(While { condition, body }) => {
                            queue.push_front(((*condition).into(), parent));
                            process_block(body, parent, &mut queue);
                        }
                        expression => {
                            walker(db, expression_id.into(), parent, walker_context).unwrap();
                        },
                    }
                }
                decl => todo!("{decl:?}"),
            }
        }
    }
}

#[derive(Default, Clone, Debug)]
pub struct NodeDatabase {
    pub module_declarations: HashMap<ModuleDeclarationID, ModuleDeclaration>,
    pub struct_declarations: HashMap<StructDeclarationID, StructDeclaration>,
    pub function_declarations: HashMap<FunctionDeclarationID, FunctionDeclaration>,
    pub expressions: HashMap<ExpressionID, Expression>,
    pub blocks: HashMap<BlockID, Block>,
    pub ids: HashMap<NodeID, Identifier>,
    pub id_generator: IDGenerator,
}

impl NodeDatabase {
    fn new() -> Self {
        Self::default()
    }

    pub fn get_function_declaration_id_from_identifier(&self, name: impl Into<Identifier>) -> Result<FunctionDeclarationID> {
        let name: Identifier = name.into();
        for (function_declaration_id, function_declaration) in self.function_declarations.iter() {
            if function_declaration.identifier == name {
                return Ok(*function_declaration_id);
            }
        }

        bail!(format!("failed to find function declaration ID for identifier {name:?}"));
    }

    fn new_module_declaration(&mut self, declaration: ModuleDeclaration) -> ModuleDeclarationID {
        let id = self.new_node_id_for_identifier(declaration.identifier.clone());
        self.module_declarations.insert(id, declaration);

        id
    }

    fn new_struct_declaration(&mut self, declaration: StructDeclaration) -> StructDeclarationID {
        // TODO: what to do about name collisions?
        let id = self.new_node_id_for_identifier(declaration.identifier.clone());
        self.struct_declarations.insert(id, declaration);

        id
    }

    fn new_node_id_for_identifier<T: From<ID> + Into<NodeID> + Copy>(
        &mut self,
        name: Identifier,
    ) -> T {
        let id = self.new_id::<T>();
        self.ids.insert(id.into(), name.clone());
        id
    }

    fn new_id<T: From<ID> + Into<NodeID> + Copy>(&mut self) -> T {
        self.id_generator.new_id::<T>()
    }

    fn get_mut_module_ref(
        &mut self,
        module_id: &ModuleDeclarationID,
    ) -> Option<&mut ModuleDeclaration> {
        self.module_declarations.get_mut(module_id)
    }

    fn new_function_declaration(
        &mut self,
        declaration: FunctionDeclaration,
    ) -> FunctionDeclarationID {
        let id = self.new_node_id_for_identifier(declaration.identifier.clone());
        self.function_declarations.insert(id, declaration);

        id
    }

    fn new_block(&mut self, block: Block) -> BlockID {
        let id = self.new_id();
        self.blocks.insert(id, block);
        id
    }

    fn new_expression(&mut self, expression: Expression) -> ExpressionID {
        let id = self.new_id();
        self.expressions.insert(id, expression);
        id
    }

    fn get_declaration(&self, declaration_id: DeclarationID) -> Option<Declaration> {
        match declaration_id {
            DeclarationID::ModuleDeclarationID(module_declaration_id) => self
                .module_declarations
                .get(&module_declaration_id)
                .map(|module_declaration| Declaration::Module(module_declaration.clone())),
            DeclarationID::StructDeclaration(struct_declaration_id) => self
                .struct_declarations
                .get(&struct_declaration_id)
                .map(|struct_declaration| Declaration::Struct(struct_declaration.clone())),
            DeclarationID::FunctionDeclaration(function_declaration_id) => self
                .function_declarations
                .get(&function_declaration_id)
                .map(|function_declaration| Declaration::Function(function_declaration.clone())),
        }
    }

    fn get_node(&self, node_id: NodeID) -> Option<Node> {
        match node_id {
            NodeID::Statement(StatementID::Declaration(declaration_id))
            | NodeID::Declaration(declaration_id) => self
                .get_declaration(declaration_id)
                .map(|declaration| Node::Statement(Statement::Declaration(declaration))),

            NodeID::Statement(StatementID::Expression(expression_id)) => self
                .expressions
                .get(&expression_id)
                .map(|expression| Node::Statement(Statement::Expression(expression.clone()))),
            NodeID::Block(block_id) => self.blocks.get(&block_id).map(|block| {
                Node::Statement(Statement::Expression(Expression::Block(block_id)))
            }),
            _ => todo!("not implemented {:?}", node_id),
        }
    }
}
