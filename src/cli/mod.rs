use anyhow::Result;
use clap::{command, Parser, Subcommand};

use crate::{
    codegen::generate_mlir,
    parser::parse,
    typed_ast::{self, type_ast},
};

#[derive(Parser)]
struct Cli {
    #[command(subcommand)]
    command: SubCommands,
}

#[derive(Subcommand)]
enum SubCommands {
    Run {
        path: Option<String>,
    },
    Build {
        #[arg(long)]
        emit_mlir: bool,
        #[arg(long)]
        emit_llvmir: bool,
        path: Option<String>,
    },
}

pub fn exec_cli() -> Result<()> {
    let cli = Cli::parse();

    match cli.command {
        SubCommands::Run { path } => {
            let path = path.unwrap_or("./main.ts".to_string());
            let contents = std::fs::read_to_string(&path)?;
            let ast = parse(&contents)?;
            let typed_program = type_ast(ast)?;
            let engine = generate_mlir(typed_program, false)?;
            unsafe { engine.invoke_packed("main", &mut [])? };
        }
        SubCommands::Build {
            emit_mlir,
            emit_llvmir,
            path,
        } => {
            let path = path.unwrap_or("./main.ts".to_string());
            let contents = std::fs::read_to_string(&path)?;
            let ast = parse(&contents)?;
            let typed_program = type_ast(ast)?;
            let engine = generate_mlir(typed_program, emit_mlir)?;
            if emit_llvmir {
                engine.dump_to_object_file("testllvm.ir");
            }
        }
    }

    Ok(())
}
