use anyhow::bail;
use anyhow::Result;
use std::collections::BTreeMap;

use crate::ir::{Instruction, IrProgram, SSAID};
use crate::parser::AccessModes;

#[derive(Debug)]
pub enum VariableState {
    Ready,
    Borrowed,
    MutBorrowed,
    Moved,
}

pub struct BorrowChecker {
    variable_states: BTreeMap<SSAID, VariableState>,
}

impl BorrowChecker {
    pub fn new() -> Self {
        Self {
            variable_states: BTreeMap::new(),
        }
    }

    pub fn check(&mut self, ir_program: IrProgram) -> Result<()> {
        println!("vars: {:#?}", ir_program.ssa_variables);
        for block in ir_program.blocks.into_values() {
            for instruction in block.instructions {
                println!("instruction {instruction:#?} state {:#?}", self.variable_states);
                match instruction {
                    Instruction::Call(function_id, args ) => {
                        ()
                    }
                    Instruction::Assign(id) => {
                        self.variable_states.insert(id, VariableState::Ready);
                    }
                    Instruction::Borrow(id) => match self.variable_states.get(&id) {
                        Some(VariableState::Ready) => {
                            self.variable_states.insert(id, VariableState::Borrowed);
                        }
                        Some(VariableState::Borrowed) => (),
                        Some(VariableState::MutBorrowed) => {
                            bail!(format!(
                                "variable {} was already mutably borrowed",
                                ir_program
                                    .ssa_variables
                                    .get(&id)
                                    .unwrap()
                                    .original_variable
                                    .0
                            ))
                        }
                        None => bail!(format!("Failed to borrow, Variable {} was not in any state, this should not be possible", ir_program
                                    .ssa_variables
                                    .get(&id)
                                    .unwrap()
                                    .original_variable
                                    .0
                            )),

                        Some(VariableState::Moved) => {
                            bail!(format!(
                                "variable {} was already moved",
                                ir_program
                                    .ssa_variables
                                    .get(&id)
                                    .unwrap()
                                    .original_variable
                                    .0
                            ))
                        }
                    },
                    Instruction::MutBorrow(id) => match self.variable_states.get(&id) {
                        Some(VariableState::Ready) => {
                            self.variable_states.insert(id, VariableState::MutBorrowed);
                        }
                        e => bail!(format!("can not mut borrow a variable {} which is in state {e:?}",
                            
                            ir_program
                                .ssa_variables
                                .get(&id)
                                .unwrap()
                                .original_variable
                                .0
                             ))
                    },
                    Instruction::BorrowEnd(id) => {
                        let old_state =  self.variable_states.insert(id, VariableState::Ready );          match old_state {
                            Some(VariableState::Borrowed) => (),
                            e => bail!("can not unborrow a variabled which is in state: {e:?}")
                        }       
                        
                           }

                    Instruction::MutBorrowEnd(id) => {
                        let old_state =  self.variable_states.insert(id, VariableState::Ready );          match old_state {
                            Some(VariableState::Ready) => (),
                            e => bail!("can not un mutborrow a variabled which is in state: {e:?}")
                        }       
                        
                           }



                    Instruction::Drop(id) | Instruction::Move(id) => match self.variable_states.get(&id) {
                        Some(VariableState::Ready) => {
                            self.variable_states.insert(id, VariableState::Moved);
                        }
                        e => bail!(format!(
                            "variable {} was already {e:?}",
                            ir_program
                                .ssa_variables
                                .get(&id)
                                .unwrap()
                                .original_variable
                                .0
                        )),
                    },
                }
            }
        }

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use crate::cli::load_program;

    use super::*;
    use crate::{ir::IrGenerator, parser::parse, typed_ast::type_ast};
    use anyhow::Result;
    use rstest::rstest;
    use std::path::PathBuf;

    #[rstest]
    fn test_borrow_checker(#[files("./ir_test_programs/test_*.ts")] path: PathBuf) -> Result<()> {
        let program = load_program(Some(path.to_str().unwrap().to_string()))?;
        let ast = parse(&program)?;
        let typed_program = type_ast(ast)?;

        let ir_generator = IrGenerator::new();
        let ir_progam = ir_generator.convert_to_ssa(typed_program);
        let mut borrow_checker = BorrowChecker::new();
        let analysis_result = borrow_checker.check(ir_progam);

        insta::assert_snapshot!(
            format!(
                "test_borrow_checking{}",
                path.file_name().unwrap().to_str().unwrap()
            ),
            format!("{:#?}", analysis_result)
        );
        Ok(())
    }
}
