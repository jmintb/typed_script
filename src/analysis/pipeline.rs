use crate::{
    analysis::{
        borrow_checker,
        free_dead_resources::{self, insert_free},
    },
    ir::IrProgram,
};
use anyhow::Result;

use super::{
    borrow_checker::BorrowChecker,
    liveness_analysis::{self, calculate_livenss},
};

pub fn transform_ir(ir_program: IrProgram) -> Result<IrProgram> {
    let liveness = calculate_livenss(&ir_program)?;
    let ir_program = insert_free(liveness, ir_program);
    let mut borrow_checker = BorrowChecker::new();
    borrow_checker.check(&ir_program)?;

    Ok(ir_program)
}
