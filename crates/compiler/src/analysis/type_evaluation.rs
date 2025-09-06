use super::ir_transformer::IrInterpreter;
use super::ir_transformer::TransformContext;
use crate::ast::identifiers::FunctionDeclarationID;
use crate::ir::BlockId;
use crate::ir::Instruction;
use crate::ir::IrProgram;
use crate::ir::Ssaid;
use crate::types::ArrayType;
use crate::types::ArrayTypeID;
use crate::types::FlatEntityStore;
use crate::types::Type;
use anyhow::bail;
use anyhow::Result;
use std::collections::btree_map::BTreeMap;
use tracing::debug;

#[derive(Clone, Default)]
pub struct IrProgramTypes {
    pub array_types: FlatEntityStore<ArrayType, ArrayTypeID>,
    pub variable_types: BTreeMap<Ssaid, Type>,
}

pub fn evaluate_types(
    ir_program: &IrProgram,
) -> Result<BTreeMap<FunctionDeclarationID, IrProgramTypes>> {
    let mut types_in_functions: BTreeMap<FunctionDeclarationID, IrProgramTypes> = BTreeMap::new();

    for function_id in ir_program.control_flow_graphs.keys() {
        let ir_interpreter: IrInterpreter<'_, IrProgramTypes> = IrInterpreter::new(
            ir_program.control_flow_graphs.get(function_id).unwrap(),
            ir_program,
        );

        let types = ir_interpreter.transform(&mut check_types)?;

        types_in_functions.insert(*function_id, types);
    }

    Ok(types_in_functions)
}

fn check_types(
    instruction_counter: usize,
    ctx: &mut TransformContext,
    block_id: &BlockId,
    bc_ctx: &mut IrProgramTypes,
) -> Result<usize> {
    let block = ctx.scope.blocks.get_mut(block_id).unwrap();

    let Some(instruction) = block.instructions.get(instruction_counter) else {
        return Ok(0);
    };

    match instruction {
        Instruction::InitArray(elements, receiver) => {
            let first_element = elements[0];
            let element_type = ctx.ssa_variable_types[&first_element];

            let array_type = ArrayType {
                element_type,
                length: elements.len(),
            };
            let type_id = bc_ctx.array_types.insert(array_type);
            bc_ctx
                .variable_types
                .insert(*receiver, Type::Array(type_id));
            debug!("set type {:?} for variable {}", type_id, receiver.0);
        }

        Instruction::Assign(result, value) => {
            if let Some(r#type) = bc_ctx.variable_types.get(value) {
                bc_ctx.variable_types.insert(*result, *r#type);
            }
        }

        Instruction::ArrayLookup { array, result, .. } => {
            let Some(Type::Array(array_variable_type_id)) = bc_ctx.variable_types.get(array) else {
                bail!("expected to find array type for {}", array.0);
            };

            let array_type = bc_ctx
                .array_types
                .get(*array_variable_type_id)
                .expect("type must exist at this point");
            bc_ctx
                .variable_types
                .insert(*result, array_type.element_type);
            debug!(
                "set type {:#?} for variable {}",
                array_type.element_type, result.0
            );
        }
        _ => (),
    }

    Ok(instruction_counter + 1)
}
