use anyhow::bail;
use anyhow::Result;
use std::collections::BTreeMap;
use tracing::debug;

use crate::analysis::ir_transformer::IrInterpreter;
use crate::analysis::ir_transformer::TransformContext;
use crate::ir::BlockId;

use crate::ir::{Instruction, IrProgram, Ssaid};

#[derive(Debug, Clone, Copy)]
pub enum VariableState {
    Ready,
    Borrowed,
    MutBorrowed,
    Moved,
}

#[derive(Clone, Default, Debug)]
struct BorrowCheckerState {
    block_states: BTreeMap<BlockId, BTreeMap<Ssaid, VariableState>>,
}

pub fn ge_variable_state(lhs: VariableState, rhs: VariableState) -> bool {
    match lhs {
        VariableState::Ready => false, // always false because rhs=Ready is caught in first match case.
        VariableState::Borrowed => match rhs {
            VariableState::Ready | VariableState::Borrowed => true,
            VariableState::Moved => false,
            VariableState::MutBorrowed => false,
        },
        VariableState::MutBorrowed => match rhs {
            VariableState::Ready | VariableState::Borrowed | VariableState::MutBorrowed => true,
            VariableState::Moved => false,
        },
        VariableState::Moved => true,
    }
}

fn stricter_variable_state(current: VariableState, new: VariableState) -> VariableState {
    if ge_variable_state(current, new) {
        current
    } else {
        new
    }
}

fn check_instruction(
    instruction_counter: usize,
    ctx: &mut TransformContext,
    block_id: &BlockId,
    bc_ctx: &mut BorrowCheckerState,
) -> Result<usize> {
    debug!("block states: {:#?}", bc_ctx.block_states);
    let variable_states = if let Some(state) = bc_ctx.block_states.get_mut(block_id) {
        debug!("founding existing variable state for {block_id}");
        state
    } else if block_id == &ctx.scope.control_flow_graph.entry_point {
        debug!("inserting new variable state map for entry point {block_id}");
        bc_ctx.block_states.insert(*block_id, BTreeMap::new());
        bc_ctx.block_states.get_mut(block_id).unwrap()
    } else {
        debug!(
            "generating new variable based on parents variable states {block_id} {:?}",
            bc_ctx.block_states
        );
        let parents = {
            let mut parents: Vec<BlockId> = ctx
                .scope
                .control_flow_graph
                .direct_predecessors(block_id)
                .collect();
            while parents.is_empty()
                || !parents
                    .iter()
                    .all(|parent| bc_ctx.block_states.contains_key(parent))
            {
                let parent_successors: Vec<BlockId> = parents
                    .iter()
                    .flat_map(|parent| ctx.scope.control_flow_graph.successors(parent).unwrap())
                    .flatten()
                    .collect();
                let new_parents: Vec<BlockId> = parents
                    .iter()
                    .flat_map(|parent| ctx.scope.control_flow_graph.direct_predecessors(parent))
                    .filter(|new_parent| !parent_successors.contains(new_parent))
                    .collect();

                if new_parents.is_empty() {
                    bail!("failed to find parents")
                }

                parents = new_parents
            }

            parents
        };

        let mut ctx: BTreeMap<Ssaid, VariableState> = BTreeMap::new();
        for state in parents
            .into_iter()
            .map(|parent| bc_ctx.block_states.get(&parent).unwrap())
        {
            for (key, val) in state {
                ctx.entry(*key)
                    .and_modify(|existing_state| {
                        *existing_state = stricter_variable_state(*existing_state, *val)
                    })
                    .or_insert(*val);
            }
        }

        bc_ctx.block_states.insert(*block_id, ctx);
        bc_ctx.block_states.get_mut(block_id).unwrap()
    };

    debug!(
        "checking instruction {} in block {} with variable states {:#?}",
        instruction_counter, block_id, variable_states
    );
    let block = ctx.scope.blocks.get_mut(block_id).unwrap();
    let Some(instruction) = block.instructions.get(instruction_counter) else {
        return Ok(0);
    };
    debug!(
        "checking instruction {:?} {:?} {}",
        instruction, variable_states, block_id
    );

    match instruction {
        // TODO: Investigate if the result SSA variable is released and borrow checked properly.
        Instruction::Addition(_, _, result) => {
            variable_states.insert(*result, VariableState::Ready);
        }
        Instruction::GreaterThan(_, _, result) => {
            variable_states.insert(*result, VariableState::Ready);
        }
        Instruction::InitArray(_, result) => {
            variable_states.insert(*result, VariableState::Ready);
        }
        Instruction::ArrayLookup { result, .. } => {
            variable_states.insert(*result, VariableState::Ready);
        }
        Instruction::AssignFnArg(id, _position) => {
            variable_states.insert(*id, VariableState::Ready);
        }
        Instruction::Call(_function_id, _args, result) => {
            variable_states.insert(*result, VariableState::Ready);
        }
        Instruction::Assign(to, _from) => {
            variable_states.insert(*to, VariableState::Ready);
        }
        Instruction::AnonymousValue(id) => {
            variable_states.insert(*id, VariableState::Ready);
        }
        Instruction::Borrow(id) => match variable_states.get(id) {
            Some(VariableState::Ready) => {
                variable_states.insert(*id, VariableState::Borrowed);
            }
            Some(VariableState::Borrowed) => (),
            Some(VariableState::MutBorrowed) => {
                bail!(format!(
                    "variable {} in block {} was already mutably borrowed",
                    ctx.ssa_variables.get(id).unwrap().original_variable.0,
                    block_id.0
                ))
            }
            None => bail!(format!(
                "Failed to borrow, Variable {} was not in any state, this should not be possible",
                ctx.ssa_variables.get(id).unwrap().original_variable.0
            )),

            Some(VariableState::Moved) => {
                bail!(format!(
                    "variable {} in block {} was already moved ",
                    ctx.ssa_variables.get(id).unwrap().original_variable.0,
                    block_id.0
                ))
            }
        },
        Instruction::MutBorrow(id) => match variable_states.get(id) {
            Some(VariableState::Ready) => {
                variable_states.insert(*id, VariableState::MutBorrowed);
            }
            e => bail!(format!(
                "can not mut borrow a variable {} which is in state {e:?}",
                ctx.ssa_variables.get(id).unwrap().original_variable.0
            )),
        },
        Instruction::BorrowEnd(id) => {
            let old_state = variable_states.insert(*id, VariableState::Ready);
            match old_state {
                Some(VariableState::Borrowed) => (),
                e => bail!("can not unborrow variabled {id:?} which is in state: {e:?}"),
            }
        }

        Instruction::MutBorrowEnd(id) => {
            let old_state = variable_states.insert(*id, VariableState::Ready);
            match old_state {
                Some(VariableState::Ready) => (),
                e => bail!("can not un mutborrow a variabled which is in state: {e:?}"),
            }
        }

        Instruction::Drop(id) | Instruction::Move(id) => match variable_states.get(id) {
            Some(VariableState::Ready) => {
                variable_states.insert(*id, VariableState::Moved);
            }
            e => bail!(format!(
                "variable {} in block {} was already {e:?}",
                ctx.ssa_variables.get(id).unwrap().original_variable.0,
                block_id.0
            )),
        },
        _ => (),
    }

    Ok(instruction_counter + 1)
}

pub fn check(ir_program: &IrProgram) -> Result<()> {
    for function_id in ir_program.control_flow_graphs.keys() {
        let interpreter = IrInterpreter::<BorrowCheckerState>::new(
            ir_program.control_flow_graphs.get(function_id).unwrap(),
            ir_program,
        );
        interpreter.transform(&mut check_instruction)?;
    }

    Ok(())
}

#[cfg(test)]
mod test {

    use super::*;

    use crate::compiler::produce_ir;
    use anyhow::Result;
    use rstest::rstest;
    use std::path::PathBuf;
    use tracing::debug;

    #[rstest]
    #[test_log::test]
    fn test_borrow_checker(#[files("./ir_test_programs/test_*.ts")] path: PathBuf) -> Result<()> {
        let ir_program = produce_ir(path.to_str().unwrap())?;
        let liveness = crate::analysis::liveness_analysis::calculate_livenss(&ir_program)?;
        let ir_program =
            crate::analysis::free_dead_resources::insert_free(liveness.clone(), ir_program);

        // debug!("CFG: {:#?}", ir_program.control_flow_graphs);
        let analysis_result = check(&ir_program);
        debug!(
            "transformed IR program: {} \n liveness {:#?}",
            ir_program, liveness
        );
        debug!("cfg: {} ", ir_program.entry_point_cfg());

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
