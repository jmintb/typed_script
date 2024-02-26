use anyhow::bail;
use anyhow::Result;
use std::collections::BTreeMap;

use crate::ir::{Instruction, IrProgram, SSAID};

pub enum VariableState {
    Ready,
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
        for block in ir_program.blocks.into_values() {
            for instruction in block.instructions {
                match instruction {
                    Instruction::Assign(id) => {
                        self.variable_states.insert(id, VariableState::Ready);
                    }
                    Instruction::Move(id) => match self.variable_states.get(&id) {
                        Some(VariableState::Ready) => {
                            self.variable_states.insert(id, VariableState::Moved);
                        }
                        _ => bail!(format!(
                            "variable {} was already moved",
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
                "test_well_formed_ir_{}",
                path.file_name().unwrap().to_str().unwrap()
            ),
            format!("{:#?}", analysis_result)
        );
        Ok(())
    }
}
