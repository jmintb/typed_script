use anyhow::bail;
use anyhow::Result;
use std::collections::BTreeMap;



use crate::analysis::ir_transformer::IrInterpreter;
use crate::analysis::ir_transformer::TransformContext;
use crate::ir::BlockId;

use crate::ir::{Instruction, IrProgram, SSAID};

#[derive(Debug, Clone)]
pub enum VariableState {
    Ready,
    Borrowed,
    MutBorrowed,
    Moved,
}


#[derive(Clone, Debug)]
pub struct BorrowCheckContext {
    variable_states: BTreeMap<SSAID, VariableState>,
}

impl Default for BorrowCheckContext {
    fn default() -> Self {
        todo!()
    }
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

    fn check_instruction(instruction_counter: usize, ctx: &mut TransformContext, block_id: &BlockId,  variable_states: &mut BTreeMap<SSAID, VariableState>) -> Result<usize> {
        
                let block = ctx.scope.blocks.get_mut(block_id).unwrap();
                let Some(instruction) = block.instructions.get(instruction_counter) else {
                    return Ok(0);
                };
                match instruction {
                    Instruction::Call(_function_id, _args ) => {
                        ()
                    }
                    Instruction::Assign(id) => {
                        variable_states.insert(*id, VariableState::Ready);
                    }
                    Instruction::Borrow(id) => match variable_states.get(&id) {
                        Some(VariableState::Ready) => {
                            variable_states.insert(*id, VariableState::Borrowed);
                        }
                        Some(VariableState::Borrowed) => (),
                        Some(VariableState::MutBorrowed) => {
                            bail!(format!(
                                "variable {} in block {} was already mutably borrowed",
                                ctx
                                    .ssa_variables
                                    .get(&id)
                                    .unwrap()
                                    .original_variable
                                    .0 , block_id.0
                            ))
                        }
                        None => bail!(format!("Failed to borrow, Variable {} was not in any state, this should not be possible", ctx
                                    .ssa_variables
                                    .get(&id)
                                    .unwrap()
                                    .original_variable
                                    .0
                            )),

                        Some(VariableState::Moved) => {
                            bail!(format!(
                                "variable {} in block {} was already moved ",
                                ctx
                                    .ssa_variables
                                    .get(&id)
                                    .unwrap()
                                    .original_variable
                                    .0 , block_id.0
                            ))
                        }
                    },
                    Instruction::MutBorrow(id) => match variable_states.get(&id) {
                        Some(VariableState::Ready) => {
                            variable_states.insert(*id, VariableState::MutBorrowed);
                        }
                        e => bail!(format!("can not mut borrow a variable {} which is in state {e:?}",
                            
                            ctx
                                .ssa_variables
                                .get(&id)
                                .unwrap()
                                .original_variable
                                .0
                             ))
                    },
                    Instruction::BorrowEnd(id) => {
                        let old_state =  variable_states.insert(*id, VariableState::Ready );          match old_state {
                            Some(VariableState::Borrowed) => (),
                            e => bail!("can not unborrow a variabled which is in state: {e:?}")
                        }       
                        
                           }

                    Instruction::MutBorrowEnd(id) => {
                        let old_state =  variable_states.insert(*id, VariableState::Ready );          match old_state {
                            Some(VariableState::Ready) => (),
                            e => bail!("can not un mutborrow a variabled which is in state: {e:?}")
                        }       
                        
                           }



                    Instruction::Drop(id) | Instruction::Move(id) => match variable_states.get(&id) {
                        Some(VariableState::Ready) => {
                            variable_states.insert(*id, VariableState::Moved);
                        }
                        e => bail!(format!(
                            "variable {} in block {} was already {e:?}",
                            ctx
                                .ssa_variables
                                .get(&id)
                                .unwrap()
                                .original_variable
                                .0
                    , block_id.0
                        )),
                    },
                }
                
                Ok(instruction_counter + 1)
    }


    pub fn check(&mut self, ir_program: &IrProgram) -> Result<()> {
        for function_id in ir_program.control_flow_graphs.keys() {
        let interpreter = IrInterpreter::<BTreeMap<SSAID, VariableState>>::new(ir_program.control_flow_graphs.get(function_id).cloned().unwrap(), ir_program.clone());
        interpreter.transform(&mut Self::check_instruction)?;
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
    use tracing::debug;

    #[rstest]
    #[test_log::test]
    fn test_borrow_checker(#[files("./ir_test_programs/test_*.ts")] path: PathBuf) -> Result<()> {
        let program = load_program(Some(path.to_str().unwrap().to_string()))?;
        let ast = parse(&program)?;
        let typed_program = type_ast(ast)?;

        let ir_generator = IrGenerator::new();
        let ir_program = ir_generator.convert_to_ssa(typed_program);
        let liveness = crate::analysis::liveness_analysis::calculate_livenss(&ir_program)?;
        let ir_program = crate::analysis::free_dead_resources::insert_free(liveness, ir_program);
        debug!("transformed IR program: {}", ir_program);
        debug!("CFG: {:#?}", ir_program.control_flow_graphs);
        let mut borrow_checker = BorrowChecker::new();
        let analysis_result = borrow_checker.check(&ir_program);

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
