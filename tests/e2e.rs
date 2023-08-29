use anyhow::Result;
use typed_script::compiler::jit;

#[test]
fn hello_world() -> Result<()> {
    let program = "fn main() {
        printf(\"Hello World!\");
    }";

    jit(program)?;

    Ok(())
}
