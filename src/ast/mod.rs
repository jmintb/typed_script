pub mod declarations;
pub mod identifiers;
pub mod nodes;
pub mod parser;
pub mod scopes;

use std::collections::{HashMap, VecDeque};
use anyhow::{Result, bail};

use crate::identifiers::{IDGenerator, ID};

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

#[derive(Default, Debug, Clone)]
pub struct Ast {
    modules: Vec<ModuleDeclarationID>,
    pub entry_function: FunctionDeclarationID, // TODO: this needs to be initialised properly
}

impl Ast {
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
            let parent_names: Vec<Vec<Identifier>> = parent_row
                .iter()
                .map(|parent| {
                    parent
                        .iter()
                        .map(|parent| {
                            db.ids
                                .get(parent)
                                .unwrap_or(&Identifier::new("unnamed".to_string()))
                                .clone()
                        })
                        .collect::<Vec<Identifier>>()
                })
                .collect();

            tree_rows.push(format!("{:#?}", parent_names));

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

        format!("{:#?}", tree_rows)
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
            |block: &Block,
             parent_id: Option<NodeID>,
             queue: &mut VecDeque<(NodeID, Option<NodeID>)>| {
                for &statement in block.statements.iter() {
                    match statement {
                        StatementID::Declaration(decl) => todo!(),
                        StatementID::Expression(expression_id) => {
                            queue.push_front((expression_id.into(), parent_id));
                        }
                    }
                }
            };

        let mut child_to_parent: HashMap<NodeID, NodeID> = HashMap::new();

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

                    // NEXT: finish traversal to be able to create a propper snapshot
                }
                NodeID::Block(block_id) => {
                    walker(db, block_id.into(), parent, walker_context).unwrap();
                    let block = db.blocks.get(&block_id).unwrap();
                    process_block(block, Some(block_id.into()), &mut queue);
                }
                NodeID::Statement(StatementID::Expression(expression_id)) => {
                    let expression = db.expressions.get(&expression_id).unwrap();

                    match expression {
                        Expression::If(IfStatement {
                            condition,
                            then_block,
                        }) => process_block(then_block, parent, &mut queue),
                        Expression::Ifelse(IfElseStatement {
                            condition,
                            then_block,
                            else_block,
                        }) => {
                            process_block(then_block, parent, &mut queue);
                            process_block(else_block, parent, &mut queue);
                        }
                        Expression::While(While { condition, body }) => {
                            process_block(body, parent, &mut queue);
                        }
                        expression => (),
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
