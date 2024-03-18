use std::collections::BTreeMap;

use anyhow::{bail, Result};

use crate::ir::{BlockId, FunctionId, Instruction, IrProgram, SSAID};

use super::ir_transformer::IrInterpreter;

#[derive(Clone, Debug)]
pub struct AbstractAddress {
    pub block_id: BlockId,
    pub inststruction: usize,
}

#[derive(Clone, Debug)]
pub struct AbstractAddressRange(pub AbstractAddress, pub AbstractAddress);

impl AbstractAddressRange {
    fn set_end(&mut self, address: AbstractAddress) {
        self.1 = address;
    }
}

#[derive(Clone, Debug, Default)]
pub struct VariableLiveness {
    pub variables: BTreeMap<SSAID, AbstractAddressRange>,
    pub variable_moved: BTreeMap<SSAID, bool>,
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
            .insert(variable_id, AbstractAddressRange(address.clone(), address));

        Ok(())
    }

    fn insert_variable_end(
        &mut self,
        id: SSAID,
        address: AbstractAddress,
        moved: bool,
    ) -> Result<()> {
        let Some(entry) = self.variables.get_mut(&id) else {
            bail!(format!(
                "missing entry for {id:?}, can't insert end of liveness"
            ));
        };

        entry.set_end(address);
        self.variable_moved.insert(id, moved);

        Ok(())
    }

    pub fn variabled_moved(&self, id: &SSAID) -> bool {
        *self.variable_moved.get(id).unwrap_or(&false)
    }

    fn insert_load(&mut self, loanee: SSAID, loaner: SSAID) -> Result<()> {
        self.loans
            .entry(loaner)
            .and_modify(|loans| {
                loans.push(loanee);
            })
            .or_insert(vec![loanee]);

        Ok(())
    }
}

pub fn calculate_livenss(ir_program: &IrProgram) -> Result<BTreeMap<FunctionId, VariableLiveness>> {
    let mut liveness_for_fn = BTreeMap::new();
    for function_id in ir_program.control_flow_graphs.keys() {
        let interpreter = IrInterpreter::<VariableLiveness>::new(
            ir_program
                .control_flow_graphs
                .get(function_id)
                .cloned()
                .unwrap(),
            ir_program.clone(),
        );

        let livenss = interpreter.transform(
            &mut |instruction_counter, ctx, block_id, variable_livness| {
                let block = ctx.scope.blocks.get(block_id).unwrap();
                let Some(instruction) = block.instructions.get(instruction_counter) else {
                    return Ok(0);
                };

                match instruction {
                    Instruction::Assign(id) => variable_livness.insert_variable_start(
                        *id,
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
                        )?;
                    }
                    _ => (),
                }

                Ok(instruction_counter + 1)
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
    use crate::{ir::IrGenerator, parser::parse, typed_ast::type_ast};
    use anyhow::Result;
    use rstest::rstest;
    use std::path::PathBuf;

    #[rstest]
    fn test_liveness(#[files("./ir_test_programs/test_*.ts")] path: PathBuf) -> Result<()> {
        let program = load_program(Some(path.to_str().unwrap().to_string()))?;
        let ast = parse(&program)?;
        let typed_program = type_ast(ast)?;

        let ir_generator = IrGenerator::new();
        let ir_progam = ir_generator.convert_to_ssa(typed_program);
        let analysis_result = calculate_livenss(&ir_progam);

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
