mod declarations;
mod identifiers;
mod nodes;
mod parser;

use std::collections::{HashMap, VecDeque};

use crate::identifiers::{IDGenerator, ID};

use self::{
    declarations::ModuleDeclaration,
    identifiers::{BlockID, ExpressionID, StatementID},
    nodes::{
        Block, Expression, FunctionDeclaration, Identifier, IfElseStatement, IfStatement,
        StructDeclaration, While,
    },
};
use super::ast::identifiers::{
    DeclarationID, FunctionDeclarationID, ModuleDeclarationID, NodeID, StructDeclarationID,
};

#[derive(Default, Debug, Clone)]
pub struct Ast {
    modules: Vec<ModuleDeclarationID>,
}

impl Ast {
    pub fn traverse(&self, db: &NodeDatabase) {
        let mut queue: VecDeque<NodeID> = self
            .modules
            .iter()
            .map(|module_id| NodeID::Declaration(DeclarationID::ModuleDeclarationID(*module_id)))
            .collect();

        let mut process_block = |block: &Block, queue: &mut VecDeque<NodeID>| {
            for &statement in block.statements.iter() {
                match statement {
                    StatementID::Declaration(decl) => todo!(),
                    StatementID::Expression(expression_id) => {
                        queue.push_front(expression_id.into());
                    }
                }
            }
        };

        // TODO: this is not parralellised
        while let Some(next) = queue.pop_front() {
            match next {
                NodeID::Declaration(DeclarationID::ModuleDeclarationID(module_id)) => {
                    let module_declaration = db.module_declarations.get(&module_id).unwrap();
                    for &struct_declaration in module_declaration.struct_declarations.iter() {
                        queue.push_front(struct_declaration.into());
                    }

                    for &function_declaration in module_declaration.function_declarations.iter() {
                        queue.push_front(function_declaration.into());
                    }
                }

                NodeID::Declaration(DeclarationID::FunctionDeclaration(function_id)) => {
                    let function_declaration = db.function_declarations.get(&function_id).unwrap();

                    if let Some(body) = function_declaration.body {
                        queue.push_front(body.into())
                    }

                    // NEXT: finish traversal to be able to create a propper snapshot
                }
                NodeID::Block(block_id) => {
                    let block = db.blocks.get(&block_id).unwrap();
                    process_block(block, &mut queue);
                }
                NodeID::Statement(StatementID::Expression(expression_id)) => {
                    let expression = db.expressions.get(&expression_id).unwrap();

                    match expression {
                        Expression::If(IfStatement {
                            condition,
                            then_block,
                        }) => process_block(then_block, &mut queue),
                        Expression::Ifelse(IfElseStatement {
                            condition,
                            then_block,
                            else_block,
                        }) => {
                            process_block(then_block, &mut queue);
                            process_block(else_block, &mut queue);
                        }
                        Expression::While(While { condition, body }) => {
                            process_block(body, &mut queue);
                        }
                        expression => todo!("{expression:?}"),
                    }
                }
                decl => todo!("{decl:?}"),
            }
        }
    }
}

#[derive(Default)]
pub struct NodeDatabase {
    module_declarations: HashMap<ModuleDeclarationID, ModuleDeclaration>,
    struct_declarations: HashMap<StructDeclarationID, StructDeclaration>,
    function_declarations: HashMap<FunctionDeclarationID, FunctionDeclaration>,
    expressions: HashMap<ExpressionID, Expression>,
    blocks: HashMap<BlockID, Block>,
    ids: HashMap<NodeID, Identifier>,
    id_generator: IDGenerator,
}

impl NodeDatabase {
    fn new() -> Self {
        Self::default()
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
}
