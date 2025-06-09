use anyhow::Result;
use tracing::debug;

use crate::{
    ast::{identifiers::ScopeID, parser::parse, scopes::build_program_scopes},
    ir::{IrGenerator, IrProgram},
    types::resolve_types, cli::load_program, cli::load_program_without_std_lib,
    backend::mlir::codegen::{generate_mlir, MlirGenerationConfig},
};

pub fn produce_ir(src: &str) -> Result<IrProgram> {
    let input = load_program(Some(src.to_string()))?;
    let (ast, mut node_db, messages) = parse(&input)?;
    let program_scopes = build_program_scopes(&ast, &mut node_db);
    let (expression_types, type_db) = resolve_types(&ast, &node_db, &program_scopes, ScopeID(0));
    let ir_generator = IrGenerator::new(ast, node_db, program_scopes, expression_types, type_db);
    Ok(ir_generator.convert_to_ssa())
}

pub fn produce_ir_without_std(src: &str) -> Result<IrProgram> {
    let input = load_program_without_std_lib(Some(src.to_string()))?;
    let (ast, mut node_db, messages) = parse(&input)?;
    let program_scopes = build_program_scopes(&ast, &mut node_db);
    let (expression_types, type_db) = resolve_types(&ast, &node_db, &program_scopes, ScopeID(0));
    debug!("type db: {:#?}", expression_types);
    let ir_generator = IrGenerator::new(ast, node_db, program_scopes, expression_types, type_db);
    Ok(ir_generator.convert_to_ssa())
}

pub fn jit(input: &str) -> Result<()> {
    let ir = produce_ir(input)?;

    // TODO: missing statement id to scope mapping

    let mlir_generation_config = MlirGenerationConfig {
        program: ir,
        verify_mlir: true,
    };


    let engine =  generate_mlir(mlir_generation_config)?;
    // Overall goal introduce scopes and an ID based approach NOT a whole type system.
    // TODO: be able to output IR -> stay focus on e2e pipeline
    // 2. IR -> MLIR
    Ok(unsafe { engine.invoke_packed("main", &mut []) }?)
}
