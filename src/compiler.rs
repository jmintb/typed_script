use crate::{codegen::generate_mlir, parser::parse, typed_ast::type_ast};
use anyhow::Result;

pub fn jit(input: &str) -> Result<()> {
    let ast = parse(input)?;
    let typed_program = type_ast(ast)?;
    let engine = generate_mlir(typed_program, false)?;
    Ok(unsafe { engine.invoke_packed("main", &mut []) }?)
}
