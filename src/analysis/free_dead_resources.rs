use std::collections::BTreeMap;

use crate::{
    analysis::liveness_analysis::AbstractAddress,
    ir::{BlockId, FunctionId, Instruction, IrProgram},
};

use super::liveness_analysis::VariableLiveness;

pub fn insert_free(
    variable_liveness: BTreeMap<FunctionId, VariableLiveness>,
    mut ir_program: IrProgram,
) -> IrProgram {
    let mut block_offsets = BTreeMap::<BlockId, usize>::new();
    for variable_liveness in variable_liveness.into_values() {
        for (variable_id, address) in variable_liveness.clone().variables {
            if variable_liveness.variabled_moved(&variable_id) {
                continue;
            }
            let block_offset = block_offsets.entry(address.1.block_id).or_insert(0);
            let target_block_id = address.1.block_id;
            let Some(cfg) = ir_program
                .control_flow_graphs
                .clone()
                .into_values()
                .find(|cfg| cfg.contains(&target_block_id))
            else {
                println!("failed to find cfg containing {}", target_block_id.0);

                continue;
            };
            let mut offset = 1;
            let address = if cfg.is_in_cycle(&target_block_id) {
                let target_block_id = cfg.find_cycle_successor(&target_block_id).unwrap();
                offset = 0;
                AbstractAddress {
                    block_id: *target_block_id,
                    inststruction: 0,
                }
            } else {
                address.1
            };

            let main_cfg = ir_program
                .control_flow_graphs
                .get(&FunctionId(crate::parser::TSIdentifier("main".to_string())))
                .unwrap();

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

    ir_program
}
