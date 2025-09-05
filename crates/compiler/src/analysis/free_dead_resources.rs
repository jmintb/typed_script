use std::collections::BTreeMap;

use tracing::debug;

use crate::{
    analysis::liveness_analysis::AbstractAddress,
    ast::identifiers::FunctionDeclarationID,
    ir::{BlockId, Instruction, IrProgram},
};

use super::liveness_analysis::VariableLiveness;

pub fn insert_free(
    variable_liveness: BTreeMap<FunctionDeclarationID, VariableLiveness>,
    mut ir_program: IrProgram,
) -> IrProgram {
    let mut block_offsets = BTreeMap::<BlockId, usize>::new();
    debug!(
        "variable liveness: {:#?} \n program {}",
        variable_liveness, ir_program
    );
    for variable_liveness in variable_liveness.into_values() {
        for (variable_id, address) in variable_liveness.clone().variables {
            debug!("variable: {}, address: {:#?}, ", variable_id.0, address);
            assert!(!address.end_addresses.is_empty());
            for end_address in address.end_addresses {
                if variable_liveness.variabled_moved(&variable_id, end_address.block_id) {
                    continue;
                }
                let block_offset = block_offsets.entry(end_address.block_id).or_insert(0);
                let target_block_id = end_address.block_id;
                let Some(cfg) = ir_program
                    .control_flow_graphs
                    .clone()
                    .into_values()
                    .find(|cfg| cfg.contains(&target_block_id))
                else {
                    debug!("failed to find cfg containing {}", target_block_id.0);

                    continue;
                };
                let mut offset = 1;
                let address = if cfg.is_in_cycle(&target_block_id) {
                    // debug!("{} is in cycle", variable_id.0);
                    let target_block_id = cfg
                        .find_cycle_successor(&target_block_id)
                        .unwrap_or_else(|| {
                            panic!(
                                "expected to find a successor to the cycle in {} \n {} \n {}",
                                target_block_id,
                                ir_program,
                                ir_program.entry_point_cfg()
                            )
                        });
                    offset = 0;
                    AbstractAddress {
                        block_id: target_block_id,
                        inststruction: 0,
                    }
                } else {
                    debug!("{} is not in cycle", variable_id.0);
                    end_address
                };

                debug!(
                    "inserting drop for variable {} in block {} at line {} with offset {}",
                    variable_id.0, address.block_id, address.inststruction, offset
                );

                ir_program
                    .blocks
                    .get_mut(&address.block_id)
                    .unwrap()
                    .instructions
                    .insert(
                        address.inststruction + offset + *block_offset,
                        Instruction::Drop(variable_id),
                    );

                block_offsets
                    .entry(address.block_id)
                    .and_modify(|offset| *offset += 1)
                    .or_insert(0);
            }
        }
    }

    ir_program
}

#[cfg(test)]
mod test {

    use anyhow::{bail, Result};
    use rstest::rstest;
    use std::path::PathBuf;

    #[rstest]
    #[test_log::test]
    fn test_ir_output_with_drops(
        #[files("./ir_test_programs/test_*.ts")] path: PathBuf,
    ) -> Result<()> {
        use crate::compiler::produce_ir;

        let ir_program = produce_ir(path.to_str().unwrap())?;
        let liveness = crate::analysis::liveness_analysis::calculate_livenss(&ir_program)?;
        let ir_program = crate::analysis::free_dead_resources::insert_free(liveness, ir_program);

        insta::assert_snapshot!(
            format!(
                "test_well_formed_ir_after_frees_{}",
                path.file_name().unwrap().to_str().unwrap()
            ),
            format!("{}", ir_program)
        );
        Ok(())
    }

    #[rstest]
    #[test_log::test]
    fn test_all_variables_are_dropped(
        #[files("./ir_test_programs/test_*.ts")] path: PathBuf,
    ) -> Result<()> {
        use crate::compiler::produce_ir;

        let ir_program = produce_ir(path.to_str().unwrap())?;
        let liveness = crate::analysis::liveness_analysis::calculate_livenss(&ir_program)?;
        let ir_program = crate::analysis::free_dead_resources::insert_free(liveness, ir_program);
        let liveness = crate::analysis::liveness_analysis::calculate_livenss(&ir_program)?;

        for variable_liveness in liveness.into_values() {
            for (variable_id, end_addresses) in variable_liveness.variables.clone() {
                for end_address in end_addresses.end_addresses {
                    if !variable_liveness.variabled_moved(&variable_id, end_address.block_id) {
                        bail!("variable {} was not moved in {}", variable_id.0, ir_program);
                    }
                }
            }
        }

        Ok(())
    }
}
