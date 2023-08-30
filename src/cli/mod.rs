use anyhow::Result;
use clap::{command, Parser, Subcommand};

use crate::{codegen::generate_mlir, parser::parse};

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
        #[arg(short, long)]
        emit_mlir: bool,
        #[arg(short, long)]
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
            let engine = generate_mlir(ast)?;
            unsafe { engine.invoke_packed("main", &mut [])? };
        }
        SubCommands::Build {
            emit_mlir,
            emit_llvmir,
            path,
        } => todo!(),
    }

    Ok(())
}
