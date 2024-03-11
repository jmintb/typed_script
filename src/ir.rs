use std::collections::{BTreeMap, BTreeSet, VecDeque};

use crate::{
    parser::{AccessModes, TSIdentifier, TSValue},
    typed_ast::{
        self, Array, ArrayLookup, Assign, Assignment, Decl, Operation, Return, Type, TypedAst,
        TypedExpression, TypedProgram, While,
    },
};

#[derive(Clone, Debug, Eq, PartialEq, PartialOrd, Ord, Copy)]
pub struct SSAID(usize);
#[derive(Clone, Debug, Eq, PartialEq, PartialOrd, Ord, Copy)]
pub struct BlockId(usize);
#[derive(Clone, Debug, Eq, PartialEq, PartialOrd, Ord)]
pub struct FunctionId(TSIdentifier);

#[derive(Clone, Debug)]
pub struct ControlFlowGraph {
    pub graph: BTreeMap<BlockId, Vec<BlockId>>,

    pub entry_point: BlockId,
}

impl ControlFlowGraph {
    fn new(entry_point: BlockId) -> Self {
        Self {
            graph: BTreeMap::new(),
            entry_point,
        }
    }

    fn insert(&mut self, parent: BlockId, child: BlockId) {
        self.graph
            .entry(parent)
            .and_modify(|children| children.push(child))
            .or_insert(vec![child]);
    }

    pub fn dominates(&self, node_a: BlockId, node_b: BlockId) -> bool {
        // TODO: We don't need a vecdeque.
        let mut child_queue = VecDeque::from(self.graph.get(&node_b).cloned().unwrap_or_default());
        let mut visited_nodes = BTreeSet::new();

        while let Some(child) = child_queue.pop_front() {
            // Found a loop that is not dominated.
            if visited_nodes.contains(&child) {
                return false;
            }
            visited_nodes.insert(child);

            let grand_children = self.graph.get(&child).cloned().unwrap_or_default();
            if child != node_a && !grand_children.is_empty() {
                for grand_child in grand_children {
                    child_queue.push_back(grand_child);
                }
            } else if child != node_a && grand_children.is_empty() {
                // Found a dead end
                return false;
            }

            // At this point we have found our way back to the parent and simply clear it from the queue.
        }

        true
    }

    pub fn predecessors<'a>(&'a self, id: &'a BlockId) -> impl Iterator<Item = BlockId> + 'a {
        self.graph
            .clone()
            .into_iter()
            .filter(|(_, children)| children.contains(id))
            .map(|(predecessor_id, _)| predecessor_id)
    }
}

#[derive(Clone, Debug)]
pub struct IrProgram {
    pub ssa_variables: BTreeMap<SSAID, Variable>,
    pub blocks: BTreeMap<BlockId, Block>,
    pub access_modes: BTreeMap<SSAID, AccessModes>,
    pub control_flow_graphs: BTreeMap<FunctionId, ControlFlowGraph>,
    pub entry_block: BlockId,
}

#[derive(Clone, Debug)]
pub struct Block {
    pub instructions: Vec<Instruction>,
}

impl Block {
    fn new() -> Self {
        Self {
            instructions: Vec::new(),
        }
    }
}

#[derive(Clone, Debug)]
pub enum Instruction {
    Assign(SSAID),
    Move(SSAID),
    Borrow(SSAID),
    BorrowEnd(SSAID),
    MutBorrow(SSAID),
    MutBorrowEnd(SSAID),
    Drop(SSAID),
    Call(FunctionId, Vec<SSAID>),
}

impl Instruction {
    fn get_inverse_instruction(&self) -> Option<Instruction> {
        match *self {
            Self::Borrow(id) => Some(Self::BorrowEnd(id)),
            Self::MutBorrow(id) => Some(Self::MutBorrowEnd(id)),
            _ => None,
        }
    }
}

#[derive(Clone, Debug)]
pub struct Variable {
    pub original_variable: TSIdentifier,
    id: SSAID,
}

#[derive(Clone, Debug)]
pub struct IrGenerator {
    ssa_variables: BTreeMap<SSAID, Variable>,
    blocks: BTreeMap<BlockId, Block>,
    id_count: usize,
    entry_block: BlockId,
    access_modes: BTreeMap<SSAID, AccessModes>,
    types: BTreeMap<TSIdentifier, Type>,
    control_flow_graphs: BTreeMap<FunctionId, ControlFlowGraph>,
    current_function: FunctionId,
}

impl IrGenerator {
    pub fn new() -> Self {
        let entry_block = Block {
            instructions: Vec::new(),
        };

        let entry_block_id = BlockId(0);
        let mut blocks = BTreeMap::new();
        blocks.insert(entry_block_id, entry_block);
        // Also starts from main.
        let entry_function = FunctionId(TSIdentifier("main".to_string()));

        Self {
            ssa_variables: BTreeMap::new(),
            blocks,
            id_count: 1,
            entry_block: entry_block_id,
            access_modes: BTreeMap::new(),
            types: BTreeMap::new(),
            control_flow_graphs: BTreeMap::new(),
            current_function: entry_function,
        }
    }

    fn new_ssa_id(&mut self) -> SSAID {
        let new_id = self.id_count;
        self.id_count += 1;
        SSAID(new_id)
    }

    fn add_ssa_variable(&mut self, original_variable_id: TSIdentifier) -> SSAID {
        let id = self.new_ssa_id();
        let ssa_var = Variable {
            original_variable: original_variable_id,
            id: id,
        };

        self.ssa_variables.insert(id, ssa_var);

        id
    }

    fn new_block_id(&mut self) -> BlockId {
        let new_id = self.id_count;
        self.id_count += 1;
        BlockId(new_id)
    }

    fn add_block(&mut self) -> BlockId {
        let id = self.new_block_id();
        let block = Block::new();

        self.blocks.insert(id, block);

        id
    }

    fn latest_gen_variable(&self, var_id: TSIdentifier) -> Option<SSAID> {
        self.ssa_variables
            .clone()
            .into_values()
            .filter(|ssa_var| ssa_var.original_variable == var_id)
            .fold(None, |acc, ssa_var| {
                if acc.is_none() {
                    Some(ssa_var)
                } else {
                    acc.map(|acc| if acc.id > ssa_var.id { acc } else { ssa_var })
                }
            })
            .map(|ssa_var| ssa_var.id)
    }

    pub fn convert_to_ssa(mut self, program: TypedProgram) -> IrProgram {
        for (key, val) in program.types {
            self.types.insert(key, val);
        }

        let mut current_block = self.entry_block;
        for node in program.ast {
            current_block = self.convert_statement(node, current_block);
        }

        IrProgram {
            ssa_variables: self.ssa_variables,
            blocks: self.blocks,
            entry_block: self.entry_block,
            access_modes: self.access_modes,
            control_flow_graphs: self.control_flow_graphs,
        }
    }

    fn record_cfg_connection(&mut self, parent: BlockId, child: BlockId) {
        self.control_flow_graphs
            .entry(self.current_function.clone())
            .and_modify(|cfg| cfg.insert(parent, child))
            .or_insert_with(|| {
                let mut cfg = ControlFlowGraph::new(parent);
                cfg.insert(parent, child);
                cfg
            });
    }

    fn convert_statement(&mut self, statement: TypedAst, current_block: BlockId) -> BlockId {
        match statement {
            TypedAst::Assignment(assignment) => self.convert_assignment(assignment, current_block),
            TypedAst::Expression(expression) => {
                self.convert_expression(expression, current_block).0
            }
            TypedAst::Decl(declaration) => self.convert_declaration(declaration, current_block),
        }
    }

    fn convert_assignment(&mut self, assignment: Assignment, current_block: BlockId) -> BlockId {
        let updated_block_id = self.convert_expression(assignment.expression, current_block);
        let ssa_id = self.add_ssa_variable(assignment.id);
        let assign_instruction = Instruction::Assign(ssa_id);
        self.add_instruction(updated_block_id.0, assign_instruction);
        updated_block_id.0
    }

    fn convert_block(&mut self, block: typed_ast::Block, current_block: BlockId) -> BlockId {
        let mut current_block = current_block;
        let mut parent_block = current_block;

        for statement in block.statements {
            current_block = self.convert_statement(statement, current_block);
            if current_block != parent_block {
                self.record_cfg_connection(parent_block, current_block);
                parent_block = current_block;
            }
        }

        current_block
    }

    fn get_access_instruction(&self, variable_id: SSAID) -> Instruction {
        match self
            .access_modes
            .get(&variable_id)
            .copied()
            .unwrap_or(AccessModes::Owned)
        {
            AccessModes::Let => Instruction::Borrow(variable_id),
            AccessModes::Owned => Instruction::Move(variable_id),
            AccessModes::Inout => Instruction::Move(variable_id),
        }
    }

    fn convert_expression(
        &mut self,
        expression: TypedExpression,
        current_block: BlockId,
    ) -> (BlockId, Option<SSAID>) {
        let mut current_block = current_block;
        match expression {
            TypedExpression::Call(function_id, arguments) => {
                let Type::Function(_, arg_types, _) =
                    self.types.get(&function_id).cloned().unwrap()
                else {
                    todo!()
                };

                let mut function_args = Vec::new();
                let mut free_instructions = Vec::new();
                let mut setup_instructions = Vec::new();

                for (i, arg) in arguments.into_iter().enumerate() {
                    let (new_current_block, ssa_var) = self.convert_expression(arg, current_block);
                    current_block = new_current_block;
                    if let Some(ssa_var) = ssa_var {
                        self.access_modes.insert(ssa_var, arg_types[i].access_mode);
                        let access_instruction = self.get_access_instruction(ssa_var);
                        setup_instructions.push(access_instruction.clone());
                        self.add_instruction(current_block, access_instruction);
                        function_args.push(ssa_var);

                        if let Some(release_instruction) = self
                            .get_access_instruction(ssa_var)
                            .get_inverse_instruction()
                        {
                            free_instructions.push(release_instruction);
                        }
                    }
                }
                if function_id.0 == "fwrite".to_string() {
                    println!("instructions {function_id:?} free_instructions{free_instructions:?} setup_instructions {setup_instructions:?}");
                }
                self.add_instruction(
                    current_block,
                    Instruction::Call(FunctionId(function_id), function_args),
                );

                for instruction in free_instructions {
                    self.add_instruction(current_block, instruction);
                }
            }

            TypedExpression::Value(val, _) => match val {
                TSValue::Variable(id) => {
                    let ssa_var = self.latest_gen_variable(id.clone()).unwrap();
                    if id.0.clone() == "stdoutptr".to_string() {
                        println!(
                            "access instruction: {:?}",
                            self.get_access_instruction(ssa_var)
                        );
                    }
                    // self.add_instruction(current_block, self.get_access_instruction(ssa_var));
                    return (current_block, Some(ssa_var));
                }
                _ => (),
            },

            TypedExpression::Struct(_, fields) => {
                for field in fields {
                    (current_block, _) = self.convert_expression(field, current_block);
                }
            }

            TypedExpression::StructFieldRef(var_id, _) => {
                let ssa_var = self.latest_gen_variable(var_id).unwrap();
                self.add_instruction(current_block, self.get_access_instruction(ssa_var));
            }

            TypedExpression::If(if_statement) => {
                (current_block, _) =
                    self.convert_expression(*if_statement.condition, current_block);
                current_block = self.convert_block(if_statement.then_block, current_block);
                if let Some(block) = if_statement.else_block {
                    current_block = self.convert_block(block, current_block);
                }
            }

            TypedExpression::While(While { condition, block }) => {
                let condition_block = self.add_block();
                self.record_cfg_connection(current_block, condition_block);
                current_block = condition_block;
                (current_block, _) = self.convert_expression(*condition, current_block);
                current_block = self.convert_block(block, current_block);
            }

            TypedExpression::Return(Return { expression }) => {
                if let Some(expression) = expression {
                    (current_block, _) = self.convert_expression(*expression, current_block);
                }
            }

            TypedExpression::Operation(operation) => match *operation {
                Operation::Binary(lhs, _, rhs) => {
                    (current_block, _) = self.convert_expression(lhs, current_block);
                    (current_block, _) = self.convert_expression(rhs, current_block);
                }
            },

            TypedExpression::Assign(Assign { id, expression }) => {
                (current_block, _) = self.convert_expression(*expression, current_block);
                let ssa_id = self.add_ssa_variable(id);
                let assign_instruction = Instruction::Assign(ssa_id);
                self.add_instruction(current_block, assign_instruction);
            }

            TypedExpression::Array(Array { items, .. }) => {
                for item in items {
                    (current_block, _) = self.convert_expression(item, current_block);
                }
            }

            TypedExpression::ArrayLookup(ArrayLookup {
                array_identifier,
                index_expression,
            }) => {
                (current_block, _) = self.convert_expression(*index_expression, current_block);
                let ssa_var = self.latest_gen_variable(array_identifier).unwrap();
                self.add_instruction(current_block, Instruction::Move(ssa_var));
            }
        }

        (current_block, None)
    }

    fn convert_declaration(&mut self, declaration: Decl, current_block: BlockId) -> BlockId {
        match declaration {
            Decl::Function {
                keywords,
                id,
                arguments,
                body,
                return_type,
            } => {
                if let Some(body) = body {
                    self.current_function = FunctionId(id);
                    let entry_block = self.add_block();

                    for arg in arguments {
                        let ssa_id = self.add_ssa_variable(arg.name);
                        let assign_instruction = Instruction::Assign(ssa_id);
                        self.access_modes.insert(ssa_id, arg.access_mode);
                        self.add_instruction(entry_block, assign_instruction);
                    }

                    let cfg = ControlFlowGraph::new(entry_block);
                    self.control_flow_graphs
                        .insert(self.current_function.clone(), cfg);

                    let new_block =
                        self.convert_block(typed_ast::Block { statements: body }, entry_block);
                }
            }

            _ => (),
        }

        return current_block;
    }

    fn add_instruction(&mut self, updated_block_id: BlockId, assign_instruction: Instruction) {
        self.blocks
            .get_mut(&updated_block_id)
            .unwrap()
            .instructions
            .push(assign_instruction)
    }
}

#[cfg(test)]
mod test {
    use crate::cli::load_program;

    use super::*;
    use anyhow::Result;
    use rstest::rstest;
    use std::path::PathBuf;

    #[rstest]
    fn test_ir_output(#[files("./ir_test_programs/test_*.ts")] path: PathBuf) -> Result<()> {
        use crate::{parser::parse, typed_ast::type_ast};

        let program = load_program(Some(path.to_str().unwrap().to_string()))?;
        let ast = parse(&program)?;
        let typed_program = type_ast(ast)?;

        let ir_generator = IrGenerator::new();
        let ir_progam = ir_generator.convert_to_ssa(typed_program);

        insta::assert_snapshot!(
            format!(
                "test_well_formed_ir_{}",
                path.file_name().unwrap().to_str().unwrap()
            ),
            format!("{:#?} \n {:#?}", ir_progam.blocks, ir_progam.ssa_variables)
        );
        Ok(())
    }
}
