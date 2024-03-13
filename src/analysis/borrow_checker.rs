use anyhow::bail;
use anyhow::Result;
use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::collections::VecDeque;

use crate::analysis::ir_transformer::IrInterpreter;
use crate::analysis::ir_transformer::TransformContext;
use crate::ir::Block;
use crate::ir::BlockId;
use crate::ir::FunctionId;
use crate::ir::{Instruction, IrProgram, SSAID};

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

    fn check_control_flow_graph(&mut self, ir_program: IrProgram, function_id: &FunctionId ) -> Result<()> {
        let cfg = ir_program.control_flow_graphs.get(function_id).expect("function id has no control flow graph");
        let entry_point = cfg.entry_point;
        let mut queue: VecDeque<BlockId> = VecDeque::new();
        queue.push_back(cfg.entry_point);

        let mut visited_blocks = BTreeSet::new();
        while let Some(child) = queue.pop_front() {
            for predecessor in cfg.predecessors(&child) {
                if !visited_blocks.contains(&predecessor) {
                    if cfg.dominates(child, predecessor) {
                        // TODO: remove predecssor from grandchildren, as we end up visiting it again.
                        // This logic tricky, as we need to ensure we revisit the dominated block after visting the dominator.
                        queue.push_front(predecessor);
                        queue.push_front(child);
                        queue.push_front(predecessor);
                        continue; // TODO: Continuing probably doesn't make sense here as we could have multiple unvisited predecessors I think. 
                    } else {
                        todo!("this should not be possible, but how do we handle it?");
                    } 
                }
            }

            self.check_block( child,  ir_program.clone())?;

            for &child in cfg.graph.get(&child).unwrap_or(&Vec::new()) {
                if !visited_blocks.contains(&child) {
                    queue.push_back(child);
                }
            }

            visited_blocks.insert(child);

        }

        Ok(())
    }

    fn check_instruction(instruction_counter: usize, ctx: &mut TransformContext, block: &BlockId) -> Result<(usize)> {
        
                let mut block = ctx.scope.blocks.get_mut(block).unwrap();
                let Some(instruction) = block.instructions.get(instruction_counter) else {
                    return Ok(0);
                };
                match instruction {
                    Instruction::Call(function_id, args ) => {
                        ()
                    }
                    Instruction::Assign(id) => {
                        ctx.variable_states.insert(*id, VariableState::Ready);
                    }
                    Instruction::Borrow(id) => match ctx.variable_states.get(&id) {
                        Some(VariableState::Ready) => {
                            ctx.variable_states.insert(*id, VariableState::Borrowed);
                        }
                        Some(VariableState::Borrowed) => (),
                        Some(VariableState::MutBorrowed) => {
                            bail!(format!(
                                "variable {} was already mutably borrowed",
                                ctx
                                    .ssa_variables
                                    .get(&id)
                                    .unwrap()
                                    .original_variable
                                    .0
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
                                "variable {} was already moved",
                                ctx
                                    .ssa_variables
                                    .get(&id)
                                    .unwrap()
                                    .original_variable
                                    .0
                            ))
                        }
                    },
                    Instruction::MutBorrow(id) => match ctx.variable_states.get(&id) {
                        Some(VariableState::Ready) => {
                            ctx.variable_states.insert(*id, VariableState::MutBorrowed);
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
                        let old_state =  ctx.variable_states.insert(*id, VariableState::Ready );          match old_state {
                            Some(VariableState::Borrowed) => (),
                            e => bail!("can not unborrow a variabled which is in state: {e:?}")
                        }       
                        
                           }

                    Instruction::MutBorrowEnd(id) => {
                        let old_state =  ctx.variable_states.insert(*id, VariableState::Ready );          match old_state {
                            Some(VariableState::Ready) => (),
                            e => bail!("can not un mutborrow a variabled which is in state: {e:?}")
                        }       
                        
                           }



                    Instruction::Drop(id) | Instruction::Move(id) => match ctx.variable_states.get(&id) {
                        Some(VariableState::Ready) => {
                            ctx.variable_states.insert(*id, VariableState::Moved);
                        }
                        e => bail!(format!(
                            "variable {} was already {e:?}",
                            ctx
                                .ssa_variables
                                .get(&id)
                                .unwrap()
                                .original_variable
                                .0
                        )),
                    },
                }
                
                Ok(instruction_counter + 1)
    }

    pub fn check(&mut self, ir_program: IrProgram) -> Result<()> {
        println!("checking program: {:#?}", ir_program);
        for function_id in ir_program.control_flow_graphs.keys() {
        let interpreter = IrInterpreter::new(ir_program.control_flow_graphs.get(function_id).cloned().unwrap(), ir_program.clone());

        interpreter.transform(&mut Self::check_instruction)?;
        println!("checking function {:?}", function_id);
//         self.check_control_flow_graph(ir_program.clone(), function_id)?;    
        }

        Ok(())
    }

fn check_block(&mut self,  child: BlockId, ir_program: IrProgram) -> Result<()> {
    let block = ir_program.blocks.get(&child).unwrap();
        println!("checking block: {:?} {:?}", child, block);

            for instruction in block.instructions.iter() {
                println!("instruction {instruction:#?} state {:#?}", self.variable_states);
                match instruction {
                    Instruction::Call(function_id, args ) => {
                        ()
                    }
                    Instruction::Assign(id) => {
                        self.variable_states.insert(*id, VariableState::Ready);
                    }
                    Instruction::Borrow(id) => match self.variable_states.get(&id) {
                        Some(VariableState::Ready) => {
                            self.variable_states.insert(*id, VariableState::Borrowed);
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
                            self.variable_states.insert(*id, VariableState::MutBorrowed);
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
                        let old_state =  self.variable_states.insert(*id, VariableState::Ready );          match old_state {
                            Some(VariableState::Borrowed) => (),
                            e => bail!("can not unborrow a variabled which is in state: {e:?}")
                        }       
                        
                           }

                    Instruction::MutBorrowEnd(id) => {
                        let old_state =  self.variable_states.insert(*id, VariableState::Ready );          match old_state {
                            Some(VariableState::Ready) => (),
                            e => bail!("can not un mutborrow a variabled which is in state: {e:?}")
                        }       
                        
                           }



                    Instruction::Drop(id) | Instruction::Move(id) => match self.variable_states.get(&id) {
                        Some(VariableState::Ready) => {
                            self.variable_states.insert(*id, VariableState::Moved);
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
