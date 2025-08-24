use crate::{
    analysis::free_dead_resources::insert_free,
    ir::IrProgram,
};
use anyhow::Result;

use super::{
    borrow_checker::BorrowChecker,
    liveness_analysis::calculate_livenss,
    type_evaluation::evaluate_types,
};

pub fn transform_ir(ir_program: IrProgram) -> Result<IrProgram> {
    let liveness = calculate_livenss(&ir_program)?;
    let ir_program = insert_free(liveness, ir_program);
    let _ = evaluate_types(&ir_program);
    let mut borrow_checker = BorrowChecker::new();
    borrow_checker.check(&ir_program)?;

    Ok(ir_program)
}
