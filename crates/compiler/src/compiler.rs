use crate::analysis::pipeline::transform_ir;
use anyhow::Result;
use melior::ExecutionEngine;
use tracing::debug;

use crate::{
    ast::{identifiers::ScopeID, parser::parse, scopes::build_program_scopes},
    backend::mlir::codegen::{generate_mlir, MlirGenerationConfig},
    cli::load_program,
    cli::load_program_without_std_lib,
    ir::{IrGenerator, IrProgram},
    types::resolve_types,
};

use crate::analysis::type_evaluation::evaluate_types;

pub fn produce_ir(src: &str) -> Result<IrProgram> {
    let input = load_program(Some(src.to_string()))?;
    let (ast, mut node_db, _messages) = parse(&input)?;
    let program_scopes = build_program_scopes(&ast, &mut node_db);
    let (expression_types, type_db) = resolve_types(&ast, &node_db, &program_scopes, ScopeID(0));
    let ir_generator = IrGenerator::new(ast, node_db, expression_types, type_db);
    Ok(ir_generator.convert_to_ssa())
}

pub fn produce_ir_without_std(src: &str) -> Result<IrProgram> {
    let input = load_program_without_std_lib(Some(src.to_string()))?;
    let (ast, mut node_db, _messages) = parse(&input)?;
    let program_scopes = build_program_scopes(&ast, &mut node_db);
    let (expression_types, type_db) = resolve_types(&ast, &node_db, &program_scopes, ScopeID(0));
    debug!("type db: {:#?}", expression_types);
    let ir_generator = IrGenerator::new(ast, node_db, expression_types, type_db);
    Ok(ir_generator.convert_to_ssa())
}

pub fn compile_with_analysis(input: &str) -> Result<ExecutionEngine> {
    let ir = produce_ir(input)?;
    let transformed_ir = transform_ir(ir)?;
    let types = evaluate_types(&transformed_ir)?;

    // TODO: missing statement id to scope mapping

    let mlir_generation_config = MlirGenerationConfig {
        program: transformed_ir,
        verify_mlir: true,
        program_types: types,
    };

    let engine = generate_mlir(mlir_generation_config)?;
    // Overall goal introduce scopes and an ID based approach NOT a whole type system.
    // TODO: be able to output IR -> stay focus on e2e pipeline
    // 2. IR -> MLIR
    Ok(engine)
}

pub fn compile(input: &str) -> Result<ExecutionEngine> {
    let ir = produce_ir(input)?;
    let types = evaluate_types(&ir)?;

    // TODO: missing statement id to scope mapping

    let mlir_generation_config = MlirGenerationConfig {
        program: ir,
        verify_mlir: true,
        program_types: types,
    };

    let engine = generate_mlir(mlir_generation_config)?;
    // Overall goal introduce scopes and an ID based approach NOT a whole type system.
    // TODO: be able to output IR -> stay focus on e2e pipeline
    // 2. IR -> MLIR
    Ok(engine)
}

pub fn jit(input: &str) -> Result<()> {
    let ir = produce_ir(input)?;
    let types = evaluate_types(&ir)?;

    // TODO: missing statement id to scope mapping

    let mlir_generation_config = MlirGenerationConfig {
        program: ir,
        verify_mlir: true,
        program_types: types,
    };

    let engine = generate_mlir(mlir_generation_config)?;
    // Overall goal introduce scopes and an ID based approach NOT a whole type system.
    // TODO: be able to output IR -> stay focus on e2e pipeline
    // 2. IR -> MLIR
    Ok(unsafe { engine.invoke_packed("main", &mut []) }?)
}
