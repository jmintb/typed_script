use std::collections::{BTreeMap, BTreeSet};

use anyhow::{Result};

use tracing::debug;

use crate::{
    control_flow_graph::ControlFlowGraph,
    ir::{BlockId, FunctionId, Instruction, IrProgram, SSAID}, ast::identifiers::FunctionDeclarationID,
};

use super::ir_transformer::IrInterpreter;

#[derive(Clone, Debug, Copy)]
pub struct AbstractAddress {
    pub block_id: BlockId,
    pub inststruction: usize,
}

#[derive(Clone, Debug)]
pub struct AbstractAddressRange {
    pub start_address: AbstractAddress,
    pub end_addresses: Vec<AbstractAddress>,
}

impl AbstractAddressRange {
    fn insert_end(&mut self, address: AbstractAddress) {
        self.end_addresses.push(address);
    }

    fn new(start_address: AbstractAddress) -> Self {
        Self {
            start_address,
            end_addresses: vec![start_address],
        }
    }
}

#[derive(Clone, Debug, Default)]
pub struct VariableLiveness {
    pub variables: BTreeMap<SSAID, AbstractAddressRange>,
    pub variable_moved: BTreeMap<SSAID, BTreeSet<BlockId>>,
    pub loans: BTreeMap<SSAID, Vec<SSAID>>,
}

impl VariableLiveness {
    fn new() -> Self {
        Self {
            variables: BTreeMap::new(),
            loans: BTreeMap::new(),
            variable_moved: BTreeMap::new(),
        }
    }

    fn insert_variable_start(
        &mut self,
        variable_id: SSAID,
        address: AbstractAddress,
    ) -> Result<()> {
        self.variables
            .entry(variable_id)
            .and_modify(|entry| entry.start_address = address)
            .or_insert(AbstractAddressRange::new(address));

        Ok(())
    }

    fn insert_move(&mut self, variable_id: SSAID, block_id: BlockId) {
        self.variable_moved
            .entry(variable_id)
            .and_modify(|drop_ids| {
                drop_ids.insert(block_id);
            })
            .or_insert(BTreeSet::from_iter(vec![block_id].into_iter()));
    }

    fn insert_variable_end(
        &mut self,
        id: SSAID,
        address: AbstractAddress,
        moved: bool,
        control_flow_graph: &ControlFlowGraph<BlockId>,
    ) -> Result<()> {
        let _variables = self.variables.clone();
        let Some(entry) = self.variables.get_mut(&id) else {
            self.variables
                .insert(id, AbstractAddressRange::new(address));
            if moved {
                self.insert_move(id, address.block_id);
            }
            return Ok(());
        };

        if let Some(_end_in_current_block) = entry
            .end_addresses
            .iter()
            .position(|end_address| end_address.block_id == address.block_id)
        {
            return Ok(());
        } else {
            let entry_clone = entry.clone();
            if entry_clone
                .end_addresses
                .iter()
                .enumerate()
                .any(|(_, end_address)| {
                    control_flow_graph
                        .cycle_aware_successors(&address.block_id)
                        .unwrap()
                        .into_iter()
                        .flatten()
                        .collect::<Vec<BlockId>>()
                        .contains(&end_address.block_id)
                })
            {
                return Ok(());
            }
            entry.end_addresses.push(address);
            if moved {
                self.insert_move(id, address.block_id);
            }
        }

        Ok(())
    }

    // TODO: next use reverse traverself to calcuate liveness. If two blocks diverge keep end addresses.

    pub fn variabled_moved(&self, id: &SSAID, block_id: BlockId) -> bool {
        self.variable_moved
            .get(id)
            .map(|block_ids| block_ids.contains(&block_id))
            .unwrap_or(false)
    }
}

pub fn calculate_livenss(ir_program: &IrProgram) -> Result<BTreeMap<FunctionDeclarationID, VariableLiveness>> {
    debug!("calculating livenss for program: {ir_program}");

    let mut liveness_for_fn = BTreeMap::new();
    for (function_id, control_flow_graph) in ir_program.control_flow_graphs.clone() {
        debug!(
            "control flow graph: {}: {}\n predecessors: {:#?}",
            function_id.0,
            control_flow_graph,
            control_flow_graph
                .cycle_aware_successors(&control_flow_graph.entry_point)
                .unwrap()
        );
        let interpreter = IrInterpreter::<VariableLiveness>::new_reversed(
            ir_program
                .control_flow_graphs
                .get(&function_id)
                .cloned()
                .unwrap(),
            ir_program.clone(),
        );

        let livenss = interpreter.transform(
            &mut |instruction_counter, ctx, block_id, variable_livness| {
                debug!(
                    "liveness for {} at instruction {}",
                    block_id, instruction_counter
                );
                let block = ctx.scope.blocks.get(block_id).unwrap();
                let Some(instruction) = block.instructions.get(instruction_counter) else {
                    return Ok(block.instructions.len());
                };

                match instruction {
                    Instruction::Assign(to, from) => variable_livness.insert_variable_start(
                        *to,
                        AbstractAddress {
                            block_id: *block_id,
                            inststruction: instruction_counter,
                        },
                    )?,
                    Instruction::BorrowEnd(id) | Instruction::MutBorrowEnd(id) => {
                        variable_livness.insert_variable_end(
                            *id,
                            AbstractAddress {
                                block_id: *block_id,
                                inststruction: instruction_counter,
                            },
                            false,
                            &ctx.scope.control_flow_graph,
                        )?;
                    }
                    Instruction::Move(id) | Instruction::Drop(id) => {
                        variable_livness.insert_variable_end(
                            *id,
                            AbstractAddress {
                                block_id: *block_id,
                                inststruction: instruction_counter,
                            },
                            true,
                            &ctx.scope.control_flow_graph,
                        )?;
                    }
                    Instruction::Call(_, _, to) => {
                    variable_livness.insert_variable_start(
                        *to,
                        AbstractAddress {
                            block_id: *block_id,
                            inststruction: instruction_counter,
                        },
                    )?
                    }
                    _ => (),
                }

                Ok(if instruction_counter == 0 {
                    block.instructions.len()
                } else {
                    instruction_counter - 1
                })
            },
        )?;

        liveness_for_fn.insert(function_id.clone(), livenss);
    }

    Ok(liveness_for_fn)
}

#[cfg(test)]
mod test {
    use crate::cli::load_program;

    use super::*;
    use crate::ir::IrGenerator;
    use anyhow::Result;
    use rstest::rstest;
    use std::path::PathBuf;

    #[rstest]
    fn test_liveness(#[files("./ir_test_programs/test_*.ts")] path: PathBuf) -> Result<()> {
        use crate::{ast::{parser::parse, identifiers::ScopeID, scopes::build_program_scopes}, types::resolve_types, compiler::produce_ir};

        let ir_program = produce_ir(path.to_str().unwrap())?;
        let analysis_result = calculate_livenss(&ir_program);

        insta::assert_snapshot!(
            format!(
                "test_liveness_{}",
                path.file_name().unwrap().to_str().unwrap()
            ),
            format!("{:#?}", analysis_result)
        );


        insta::assert_snapshot!(
            format!(
                "test_liveness_{}",
                path.file_name().unwrap().to_str().unwrap()
            ),
            format!("{:#?}", analysis_result)
        );

        Ok(())
    }
}
