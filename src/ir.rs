use std::{
    collections::{BTreeMap, HashMap},
    fmt::Display,
};

use anyhow::{bail, Result};
use tracing::debug;

use crate::{
    ast::{
        identifiers::{BlockID, ExpressionID, FunctionDeclarationID, ScopeID, StatementID},
        nodes::{
            AccessModes, Array, ArrayLookup, Assign, Assignment, Call, Expression, FunctionArg,
            Identifier, IfElseStatement, IfStatement, Operation, Return, StructField,
            StructFieldPath, StructInit, Type, Value, While, Operator
        },
        scopes::Scope,
        Ast, NodeDatabase,
    },
    control_flow_graph::ControlFlowGraph,
    types::{FunctionType, TypeDB},
};

#[derive(Clone, Debug, Eq, PartialEq, PartialOrd, Ord, Copy, Hash)]
pub struct SSAID(pub usize);
#[derive(Clone, Debug, Eq, PartialEq, PartialOrd, Ord, Copy, Hash)]
pub struct BlockId(pub usize);
#[derive(Clone, Debug, Eq, PartialEq, PartialOrd, Ord)]
pub struct FunctionId(pub FunctionDeclarationID);

impl Display for FunctionId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0 .0.fmt(f)
    }
}

impl Display for BlockId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&format!("block_{}", self.0))
    }
}

// TODO: next parallelize architecture based on control flow graphs and functions

#[derive(Clone, Debug)]
pub struct IrProgram {
    pub ssa_variables: BTreeMap<SSAID, Variable>,
    pub blocks: BTreeMap<BlockId, Block>,
    pub access_modes: BTreeMap<SSAID, AccessModes>,
    pub control_flow_graphs: BTreeMap<FunctionDeclarationID, ControlFlowGraph<BlockId>>,
    pub entry_block: BlockId,
    pub entry_function_id: FunctionDeclarationID,
    pub node_db: NodeDatabase,
    pub static_values: HashMap<SSAID, Value>,
}

impl IrProgram {
    pub fn entry_point_cfg(&self) -> ControlFlowGraph<BlockId> {
        self.control_flow_graphs
            .get(&self.entry_function_id)
            .unwrap()
            .clone()
    }
}

impl Display for IrProgram {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("IR:\n")?;
        for (function_id, control_flow_graph) in self.control_flow_graphs.clone() {
            f.write_fmt(format_args!("fn {}:\n", function_id.0))?;
            for block_id in control_flow_graph.clone().into_ordered_iterator() {
                let block = self.blocks.get(&block_id).unwrap();
                f.write_fmt(format_args!("{}\n", block_id))?;

                for (instruction_count, instruction) in block.instructions.iter().enumerate() {
                    f.write_fmt(format_args!(
                        "{}: {}\n",
                        instruction_count,
                        instruction.to_display_string(&self.ssa_variables)
                    ))?;
                }

                f.write_str("\n")?;
            }
        }

        f.write_str("\n")?;

        Ok(())
    }
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

#[derive(Clone, Debug, PartialEq)]
pub enum Instruction {
    Addition(SSAID, SSAID, SSAID),
    Assign(SSAID, SSAID),
    Move(SSAID),
    Borrow(SSAID),
    BorrowEnd(SSAID),
    MutBorrow(SSAID),
    MutBorrowEnd(SSAID),
    Drop(SSAID),
    Call(FunctionId, Vec<(SSAID, AccessModes)>, SSAID),
    AssignFnArg(SSAID),
    Return(Option<SSAID>),
}

impl Instruction {
    fn get_inverse_instruction(&self) -> Option<Instruction> {
        match *self {
            Self::Borrow(id) => Some(Self::BorrowEnd(id)),
            Self::MutBorrow(id) => Some(Self::MutBorrowEnd(id)),
            _ => None,
        }
    }

    pub fn to_display_string(&self, ssa_variables: &BTreeMap<SSAID, Variable>) -> String {
        match self {
            Self::Addition(lhs, rhs, result) => {
                format!(
                    "{}_{} = {}_{} + {}_{}",
                    result.0,
                    ssa_variables.get(result).unwrap().original_variable.0,
                    lhs.0,
                    ssa_variables.get(lhs).unwrap().original_variable.0,
                    rhs.0,
                    ssa_variables.get(rhs).unwrap().original_variable.0
                )
            }
            Self::Assign(to, from) => {
                format!(
                    "{}_{} = {}_{}",
                    to.0,
                    ssa_variables.get(to).unwrap().original_variable.0,
                    from.0,
                    ssa_variables.get(from).unwrap().original_variable.0
                )
            }
            Self::AssignFnArg(to) => {
                format!(
                    "{}_{} = fnarg",
                    to.0,
                    ssa_variables.get(to).unwrap().original_variable.0,
                )
            }
            Self::Move(id) => {
                format!(
                    "move({}_{})",
                    id.0,
                    ssa_variables.get(id).unwrap().original_variable.0
                )
            }

            Self::Borrow(id) => {
                format!(
                    "borrow({}_{})",
                    id.0,
                    ssa_variables.get(id).unwrap().original_variable.0
                )
            }
            Self::BorrowEnd(id) => {
                format!(
                    "borrow_end({}_{})",
                    id.0,
                    ssa_variables.get(id).unwrap().original_variable.0
                )
            }
            Self::MutBorrow(id) => {
                format!(
                    "mut_borrow({}_{})",
                    id.0,
                    ssa_variables.get(id).unwrap().original_variable.0
                )
            }
            Self::MutBorrowEnd(id) => {
                format!(
                    "mut_borrow_end({}_{})",
                    id.0,
                    ssa_variables.get(id).unwrap().original_variable.0
                )
            }
            Self::Drop(id) => {
                format!(
                    "drop({}_{})",
                    id.0,
                    ssa_variables.get(id).unwrap().original_variable.0
                )
            }
            Self::Call(function_id, args, result_id) => {
                format!(
                    "receiver_{:?} = @{}({})",
                    result_id,
                    function_id.0 .0,
                    args.iter()
                        .map(|(variable_id, access_mode)| format!(
                            "{} {}_{},",
                            access_mode,
                            variable_id.0,
                            ssa_variables.get(variable_id).unwrap().original_variable.0
                        ))
                        .fold(String::new(), |acc, next| format!("{} {}", acc, next))
                )
            }
            Self::Return(None) => "return".to_string(),
            Self::Return(Some(val)) => format!("return {}", val.0),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Variable {
    // TODO: avoid storing a copy of the identifier here
    pub original_variable: Identifier,
    id: SSAID,
}

#[derive(Clone, Debug)]
pub struct IrGenerator {
    ssa_variables: BTreeMap<SSAID, Variable>,
    blocks: BTreeMap<BlockId, Block>,
    id_count: usize,
    entry_block: BlockId,
    access_modes: BTreeMap<SSAID, AccessModes>,
    control_flow_graphs: BTreeMap<FunctionDeclarationID, ControlFlowGraph<BlockId>>,
    current_function: FunctionDeclarationID,
    node_db: NodeDatabase,
    type_db: TypeDB,
    scopes: HashMap<ScopeID, Scope>,
    types: HashMap<ExpressionID, Type>,
    entry_point_function: FunctionDeclarationID,
    static_values: HashMap<SSAID, Value>,
}

use crate::types;

impl IrGenerator {
    pub fn new(
        ast: Ast,
        node_db: NodeDatabase,
        scopes: HashMap<ScopeID, Scope>,
        expression_types: HashMap<ExpressionID, types::Type>,
        type_db: TypeDB,
    ) -> Self {
        let entry_block = Block {
            instructions: Vec::new(),
        };

        let entry_block_id = BlockId(0);
        let mut blocks = BTreeMap::new();
        blocks.insert(entry_block_id, entry_block);
        // Also starts from main.

        Self {
            ssa_variables: BTreeMap::new(),
            blocks,
            id_count: 1,
            entry_block: entry_block_id,
            access_modes: BTreeMap::new(),
            types: HashMap::new(),
            control_flow_graphs: BTreeMap::new(),
            current_function: ast.get_entry_function_id(&node_db).unwrap(),
            entry_point_function: ast.get_entry_function_id(&node_db).unwrap(),
            type_db,
            node_db,
            scopes,
            static_values: HashMap::new(),
        }
    }

    fn new_ssa_id(&mut self) -> SSAID {
        let new_id = self.id_count;
        self.id_count += 1;
        SSAID(new_id)
    }

    fn add_ssa_variable(&mut self, original_variable_id: Identifier) -> SSAID {
        let id = self.new_ssa_id();
        let ssa_var = Variable {
            original_variable: original_variable_id,
            id,
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
        debug!("add block {}", id.0);

        self.blocks.insert(id, block);

        id
    }

    fn latest_gen_variable(&self, var_id: Identifier) -> Option<SSAID> {
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

    pub fn generate_ir_program(
        mut self,
        ast: &Ast,
        node_db: &NodeDatabase,
        scopes: &HashMap<ScopeID, Scope>,
        types: &HashMap<ExpressionID, Type>,
        type_db: &TypeDB,
    ) -> IrProgram {
        // NEXT: move node_db and type_db into ir generator

        todo!()
    }

    fn convert_function_declaration(&mut self, function_declaration_id: FunctionDeclarationID) {
        let function_declaration = self
            .node_db
            .function_declarations
            .get(&function_declaration_id)
            .unwrap()
            .clone();

        // TODO: At this point we should'nt have to check such things.
        let Some(function_body_id) = function_declaration.body else {
            return;
        };

        self.current_function = function_declaration_id;
        let entry_block = self.add_block();

        for argument in function_declaration.arguments {
            self.declare_function_argument(argument, entry_block);
        }

        let cfg = ControlFlowGraph::new(entry_block);
        self.control_flow_graphs.insert(self.current_function, cfg);

        let _ = self.convert_block(function_body_id, entry_block);
    }

    // TODO NEXT: make this parallel down to function level with CFG.
    // TODO NEXT: We need to have types for each SSAID

    pub fn convert_to_ssa(mut self) -> IrProgram {
        // TODO: Switch from HashMa to Vec to avoid having to perform this conversion.
        let mut function_names: Vec<FunctionDeclarationID> = self.node_db.function_declarations.clone().into_keys().collect();
        function_names.sort();
        for function_declaration in function_names {
            self.convert_function_declaration(function_declaration);
        }

        IrProgram {
            ssa_variables: self.ssa_variables,
            blocks: self.blocks,
            entry_block: self.entry_block,
            access_modes: self.access_modes,
            control_flow_graphs: self.control_flow_graphs,
            entry_function_id: self.entry_point_function,
            node_db: self.node_db,
            static_values: self.static_values,
        }
    }

    fn record_cfg_connection(&mut self, parent: BlockId, child: BlockId) {
        debug!("record cfg connection {} -> {}", parent.0, child.0);
        self.control_flow_graphs
            .entry(self.current_function.clone())
            .and_modify(|cfg| cfg.insert_edge(parent, child))
            .or_insert_with(|| {
                let mut cfg = ControlFlowGraph::new(parent);
                cfg.insert_edge(parent, child);
                cfg
            });
    }

    fn convert_statement(&mut self, statement_id: StatementID, current_block: BlockId) -> BlockId {
        match statement_id {
            StatementID::Expression(expression_id) => {
                self.convert_expression(expression_id, current_block).0
            }
            _ => todo!(),
        }
    }

    fn convert_assignment(&mut self, assignment: Assignment, current_block: BlockId) -> BlockId {
        let (updated_block_id, Some(result_id)) =
            self.convert_expression(assignment.expression, current_block)
        else {
            panic!(
                "Expected a result from expression {:?}",
                self.node_db.expressions.get(&assignment.expression)
            );
        };

        let ssa_id = self.add_ssa_variable(assignment.id);
        let assign_instruction = Instruction::Assign(ssa_id, result_id);
        self.add_instruction(updated_block_id, assign_instruction);
        self.add_instruction(updated_block_id, self.get_access_instruction(result_id));
        updated_block_id
    }

    fn convert_block(&mut self, ast_block_id: BlockID, current_block: BlockId) -> BlockId {
        let mut current_block = current_block;
        let mut parent_block = current_block;
        current_block = self.add_block();
        self.record_cfg_connection(parent_block, current_block);

        let ast_block = self.node_db.blocks.get(&ast_block_id).unwrap().clone();

        for statement in ast_block.statements.iter() {
            current_block = self.convert_statement(*statement, current_block);
            if current_block != parent_block {
                // self.record_cfg_connection(parent_block, current_block);
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
        expression_id: ExpressionID,
        current_block: BlockId,
    ) -> (BlockId, Option<SSAID>) {
        let mut current_block = current_block;
        let expression = self
            .node_db
            .expressions
            .get(&expression_id)
            .unwrap()
            .clone();
        match expression {
            Expression::Block(ast_block) => {
                current_block = self.convert_block(ast_block, current_block);
            }
            Expression::Assignment(assignment_ment) => {
                current_block = self.convert_assignment(assignment_ment, current_block);
            }
            Expression::Call(Call {
                function_id,
                arguments,
            }) => {
                // TODO: Use actual function type and not just circumvent using declarations.
                let function_type_id = &self
                    .node_db
                    .get_function_declaration_id_from_identifier(function_id.clone())
                    .unwrap();

                let function_declaration = self
                    .node_db
                    .function_declarations
                    .get(function_type_id)
                    .unwrap()
                    .clone();

                let argument_types = function_declaration.arguments.clone();

                let mut function_args = Vec::new();
                let mut free_instructions = Vec::new();
                let mut setup_instructions = Vec::new();

                for (i, arg) in arguments.into_iter().enumerate() {
                    let (new_current_block, ssa_var) = self.convert_expression(arg, current_block);

                    current_block = new_current_block;
                    if let Some(ssa_var) = ssa_var {
                        self.access_modes
                            .insert(ssa_var, argument_types[i].access_mode);
                        let access_instruction = self.get_access_instruction(ssa_var);
                        setup_instructions.push(access_instruction.clone());
                        self.add_instruction(current_block, access_instruction);
                        function_args.push((ssa_var, argument_types[i].access_mode));

                        if let Some(release_instruction) = self
                            .get_access_instruction(ssa_var)
                            .get_inverse_instruction()
                        {
                            match release_instruction {
                                Instruction::BorrowEnd(borrowd_var) => {
                                    if !free_instructions.contains(&release_instruction) {
                                      free_instructions.push(release_instruction);
                                    }
                                }
                                _ => free_instructions.push(release_instruction)

                            }
                                                    }
                    }
                }

                // TODO: it might not always mmake sense to produce a function result.
                let function_call_result_reciever =
                    self.add_ssa_variable(Identifier::new(format!("{}_result", function_id.0)));

                self.add_instruction(
                    current_block,
                    Instruction::Call(
                        FunctionId(
                            self.node_db
                                .get_function_declaration_id_from_identifier(function_id)
                                .unwrap(),
                        ),
                        function_args,
                        function_call_result_reciever,
                    ),
                );

                for instruction in free_instructions {
                    self.add_instruction(current_block, instruction);
                }

                return (current_block, Some(function_call_result_reciever));
            }

            Expression::Value(val) => match val {
                Value::Variable(id) => {
                    let ssa_var = self.latest_gen_variable(id.clone()).unwrap();
                    // self.add_instruction(current_block, self.get_access_instruction(ssa_var));
                    return (current_block, Some(ssa_var));
                }
                _ => {
                    let ssa_var = self.declare_static_value(val, current_block);
                    return (current_block, Some(ssa_var));
                }
            },

            Expression::Struct(StructInit {
                struct_id,
                field_values,
            }) => {
                for field in field_values {
                    (current_block, _) = self.convert_expression(field, current_block);
                }
            }

            Expression::StructFieldRef(StructFieldPath {
                struct_indentifier,
                field_identifier,
            }) => {
                let ssa_var = self.latest_gen_variable(struct_indentifier).unwrap();
                self.add_instruction(current_block, self.get_access_instruction(ssa_var));
            }

            Expression::If(IfStatement {
                condition,
                then_block,
            }) => {
                let parent_block = current_block;
                (current_block, _) = self.convert_expression(condition, current_block);
                current_block = self.convert_block(then_block, current_block);
                let post_if_block = self.add_block();
                self.record_cfg_connection(current_block, post_if_block);

                current_block = post_if_block;
            }

            Expression::Ifelse(IfElseStatement {
                condition,
                then_block,
                else_block,
            }) => {
                let parent_block = current_block;
                (current_block, _) = self.convert_expression(condition, current_block);
                current_block = self.convert_block(then_block, current_block);
                let post_if_block = self.add_block();
                self.record_cfg_connection(current_block, post_if_block);
                current_block = self.convert_block(else_block, parent_block);
                self.record_cfg_connection(current_block, post_if_block);

                current_block = post_if_block;
            }

            Expression::While(While { condition, body }) => {
                let condition_block = self.add_block();
                self.record_cfg_connection(current_block, condition_block);
                current_block = condition_block;
                (current_block, _) = self.convert_expression(condition, current_block);
                let body_block = self.add_block();
                self.record_cfg_connection(condition_block, body_block);
                let body_block = self.convert_block(body, body_block);
                self.record_cfg_connection(body_block, condition_block);
                let post_loop_block = self.add_block();
                self.record_cfg_connection(condition_block, post_loop_block);
                current_block = post_loop_block;
            }

            Expression::Return(Return { expression }) => {
                if let Some(expression) = expression {
                    let (result_block, result) = self.convert_expression(expression, current_block);
                    self.add_instruction(result_block, Instruction::Return(result));
                    current_block = result_block
                } else {
                    self.add_instruction(current_block, Instruction::Return(None));
                }
            }

            Expression::Operation(operation) => match operation {
                Operation::Binary(lhs, ref operator, rhs) => {
                    let (lhs_block, lhs_id) = self.convert_expression(lhs, current_block);
                    let (rhs_block, rhs_id) = self.convert_expression(rhs, lhs_block);
                    current_block = rhs_block;

                    let Some(lhs_id) = lhs_id else {
                       panic!("left hand side expression did not produce an id, from operation: {:?}", operation.clone()) 
                    };
                    
                    let Some(rhs_id) = rhs_id else {
                       panic!("right hand side expression did not produce an id, from operation: {:?}", operation.clone()) 
                    };

                    match operator {
                        Operator::Addition => {
                            let ssa_id = self.add_ssa_variable(Identifier::new("@addition_result".to_string()));
                            let assign_instruction = Instruction::Addition(lhs_id, rhs_id, ssa_id);
                            self.add_instruction(current_block, assign_instruction);
                            self.add_instruction(
                                current_block,
                                self.get_access_instruction(lhs_id)
                            );
                            self.add_instruction(
                                current_block,
                                self.get_access_instruction(rhs_id)
                            );

                            return (current_block, Some(ssa_id));
                        }
                        _ => panic!("operator {:?} not support", operator),
                    }
                }
            },

            Expression::Assign(Assign { id, expression }) => {
                current_block =
                    self.convert_assignment(Assignment { id, expression }, current_block);
            }

            Expression::Array(Array { items }) => {
                for item in items {
                    (current_block, _) = self.convert_expression(item, current_block);
                }
            }

            Expression::ArrayLookup(ArrayLookup {
                array_identifier,
                index_expression,
            }) => {
                (current_block, _) = self.convert_expression(index_expression, current_block);
                let ssa_var = self.latest_gen_variable(array_identifier).unwrap();
                self.add_instruction(current_block, Instruction::Move(ssa_var));
            }
        }

        (current_block, None)
    }

    fn declare_function_argument(&mut self, argument: FunctionArg, current_block: BlockId) {
        let ssa_id = self.add_ssa_variable(argument.name);
        let assign_instruction = Instruction::AssignFnArg(ssa_id);
        self.access_modes.insert(ssa_id, argument.access_mode);
        self.add_instruction(current_block, assign_instruction);
    }

    fn add_instruction(&mut self, updated_block_id: BlockId, assign_instruction: Instruction) {
        self.blocks
            .get_mut(&updated_block_id)
            .unwrap()
            .instructions
            .push(assign_instruction)
    }

    fn declare_static_value(&mut self, val: Value, current_block: BlockId) -> SSAID {
        let static_ssa_id = self.add_ssa_variable(Identifier("Anonymous".to_string()));
        self.static_values.insert(static_ssa_id, val);
        let expression_ssa_id = self.add_ssa_variable(Identifier("Anonymous".to_string()));
        self.add_instruction(
            current_block,
            Instruction::Assign(expression_ssa_id, static_ssa_id),
        );
        expression_ssa_id
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::ast::parser::parse;
    use crate::ast::scopes::build_program_scopes;
    use crate::types::resolve_types;
    use anyhow::Result;
    use rstest::rstest;
    use std::path::PathBuf;

    // NEXT actual: aligns types added outside of this file

    #[rstest]
    fn test_ir_output(#[files("./ir_test_programs/test_*.ts")] path: PathBuf) -> Result<()> {
        use crate::compiler::produce_ir;

        let ir_progam = produce_ir(path.to_str().unwrap())?;

        insta::assert_snapshot!(
            format!(
                "test_well_formed_ir_{}",
                path.file_name().unwrap().to_str().unwrap()
            ),
            format!("{}", ir_progam)
        );
        Ok(())
    }

    #[rstest]
    #[test_log::test]
    fn test_control_flow_graph(
        #[files("./ir_test_programs/test_*.ts")] path: PathBuf,
    ) -> Result<()> {
        use crate::compiler::produce_ir;

        let ir_progam = produce_ir(path.to_str().unwrap())?;
        debug!("IR: {}", ir_progam);
        for (function_id, control_flow_graph) in ir_progam.control_flow_graphs {
            insta::assert_snapshot!(
                format!(
                    "test_well_formed_control_flow_graph_{}_function_{function_id:?}",
                    path.file_name().unwrap().to_str().unwrap()
                ),
                format!("{}", control_flow_graph)
            );
        }

        Ok(())
    }
}
