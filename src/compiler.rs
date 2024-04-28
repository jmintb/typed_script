use anyhow::Result;

use crate::{
    ast::{identifiers::ScopeID, parser::parse, scopes::build_program_scopes},
    types::resolve_types,
};

pub fn jit(input: &str) -> Result<()> {
    let (ast, node_db, messages) = parse(input)?;

    // TODO: missing statement id to scope mapping
    let program_scopes = build_program_scopes(&ast, &mut node_db);
    let (expression_types, type_db) = resolve_types(&ast, &node_db, &program_scopes, ScopeID(0));
    let ir = generate_ir(&ast, &node_db, &program_scopes, &expression_types, type_db);
    // Overall goal introduce scopes and an ID based approach NOT a whole type system.
    // TODO: be able to output IR -> stay focus on e2e pipeline
    // 2. IR -> MLIR
    // let engine = generate_mlir(typed_program, false)?;
    Ok(unsafe { engine.invoke_packed("main", &mut []) }?)
}
