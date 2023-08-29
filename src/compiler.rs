use crate::{codegen::generate_mlir, parser::parse};
use anyhow::Result;

pub fn jit(input: &str) -> Result<()> {
    let ast = parse(input)?;
    let engine = generate_mlir(ast)?;
    Ok(unsafe { engine.invoke_packed("main", &mut []) }?)
}
