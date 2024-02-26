use std::collections::BTreeMap;

use crate::{
    parser::{TSIdentifier, TSValue},
    typed_ast::{
        self, Array, ArrayLookup, Assign, Assignment, Decl, IfStatement, Operation, Return,
        TypedAst, TypedExpression, TypedProgram, While,
    },
};

#[derive(Clone, Debug, Eq, PartialEq, PartialOrd, Ord, Copy)]
pub struct SSAID(usize);
#[derive(Clone, Debug, Eq, PartialEq, PartialOrd, Ord, Copy)]
pub struct BlockId(usize);

#[derive(Clone, Debug)]
pub struct IrProgram {
    pub ssa_variables: BTreeMap<SSAID, Variable>,
    pub blocks: BTreeMap<BlockId, Block>,
    entry_block: BlockId,
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
}

impl IrGenerator {
    pub fn new() -> Self {
        let entry_block = Block {
            instructions: Vec::new(),
        };

        let entry_block_id = BlockId(0);
        let mut blocks = BTreeMap::new();
        blocks.insert(entry_block_id, entry_block);

        Self {
            ssa_variables: BTreeMap::new(),
            blocks,
            id_count: 1,
            entry_block: entry_block_id,
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
        let mut current_block = self.entry_block;
        for node in program.ast {
            current_block = self.convert_statement(node, current_block);
        }

        IrProgram {
            ssa_variables: self.ssa_variables,
            blocks: self.blocks,
            entry_block: self.entry_block,
        }
    }

    fn convert_statement(&mut self, statement: TypedAst, current_block: BlockId) -> BlockId {
        match statement {
            TypedAst::Assignment(assignment) => self.convert_assignment(assignment, current_block),
            TypedAst::Expression(expression) => self.convert_expression(expression, current_block),
            TypedAst::Decl(declaration) => self.convert_declaration(declaration, current_block),
        }
    }

    fn convert_assignment(&mut self, assignment: Assignment, current_block: BlockId) -> BlockId {
        let updated_block_id = self.convert_expression(assignment.expression, current_block);
        let ssa_id = self.add_ssa_variable(assignment.id);
        let assign_instruction = Instruction::Assign(ssa_id);
        self.add_instruction(updated_block_id, assign_instruction);
        updated_block_id
    }

    fn convert_block(&mut self, block: typed_ast::Block, current_block: BlockId) -> BlockId {
        let mut current_block = self.add_block();

        for statement in block.statements {
            current_block = self.convert_statement(statement, current_block);
        }

        current_block
    }

    fn convert_expression(
        &mut self,
        expression: TypedExpression,
        current_block: BlockId,
    ) -> BlockId {
        let mut current_block = current_block;
        match expression {
            TypedExpression::Call(_, arguments) => {
                for arg in arguments {
                    current_block = self.convert_expression(arg, current_block);
                }
            }

            TypedExpression::Value(val, _) => match val {
                TSValue::Variable(id) => {
                    let ssa_var = self.latest_gen_variable(id).unwrap();
                    self.add_instruction(current_block, Instruction::Move(ssa_var))
                }
                _ => (),
            },

            TypedExpression::Struct(_, fields) => {
                for field in fields {
                    current_block = self.convert_expression(field, current_block);
                }
            }

            TypedExpression::StructFieldRef(var_id, _) => {
                let ssa_var = self.latest_gen_variable(var_id).unwrap();
                self.add_instruction(current_block, Instruction::Move(ssa_var));
            }

            TypedExpression::If(if_statement) => {
                current_block = self.convert_expression(*if_statement.condition, current_block);
                current_block = self.convert_block(if_statement.then_block, current_block);
                if let Some(block) = if_statement.else_block {
                    current_block = self.convert_block(block, current_block);
                }
            }

            TypedExpression::While(While { condition, block }) => {
                current_block = self.convert_expression(*condition, current_block);
                current_block = self.convert_block(block, current_block);
            }

            TypedExpression::Return(Return { expression }) => {
                if let Some(expression) = expression {
                    current_block = self.convert_expression(*expression, current_block);
                }
            }

            TypedExpression::Operation(operation) => match *operation {
                Operation::Binary(lhs, _, rhs) => {
                    current_block = self.convert_expression(lhs, current_block);
                    current_block = self.convert_expression(rhs, current_block);
                }
            },

            TypedExpression::Assign(Assign { id, expression }) => {
                current_block = self.convert_expression(*expression, current_block);
                let ssa_id = self.add_ssa_variable(id);
                let assign_instruction = Instruction::Assign(ssa_id);
                self.add_instruction(current_block, assign_instruction);
            }

            TypedExpression::Array(Array { items, .. }) => {
                for item in items {
                    current_block = self.convert_expression(item, current_block);
                }
            }

            TypedExpression::ArrayLookup(ArrayLookup {
                array_identifier,
                index_expression,
            }) => {
                current_block = self.convert_expression(*index_expression, current_block);
                let ssa_var = self.latest_gen_variable(array_identifier).unwrap();
                self.add_instruction(current_block, Instruction::Move(ssa_var));
            }
        }

        current_block
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
                    for arg in arguments {
                        let ssa_id = self.add_ssa_variable(arg.name);
                        let assign_instruction = Instruction::Assign(ssa_id);
                        self.add_instruction(current_block, assign_instruction);
                    }
                    return self
                        .convert_block(typed_ast::Block { statements: body }, current_block);
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
