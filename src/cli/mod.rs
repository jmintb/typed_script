use anyhow::Result;
use clap::{command, Parser, Subcommand};

use crate::{codegen::generate_mlir, parser::parse, typed_ast::type_ast, compiler};


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
    Runold {
        path: Option<String>,
    },
    Build {
        #[arg(long)]
        emit_mlir: bool,
        #[arg(long)]
        emit_llvmir: bool,
        path: Option<String>,
        #[arg(long)]
        analyse: bool,
    },
}

fn load_std_lib() -> String {
    // TODO: should stdout be closed?
    "
        
extern fn fdopen(fd: integer, mode: str) -> ptr;
extern fn fclose(fd: str);
extern fn fwrite(val: str, size: integer, len: integer, file: str) -> integer;
extern fn sprintf(output: str, format: str, number: integer) -> integer;
extern fn fflush(file: str) -> integer;
extern fn sleep(time: integer) -> integer;
fn print(val: str, len: integer) {
     let stdoutptr = fdopen(1, \"w\");
     fwrite(val, len, 1, stdoutptr);
     return;
    }
    "
    .to_string()
}

pub fn load_program(path: Option<String>) -> Result<String> {
    let path = path.unwrap_or("./main.ts".to_string());
    let std_lib = load_std_lib();
    Ok(format!("{std_lib}\n {}", std::fs::read_to_string(path)?))
}

pub fn load_program_without_std_lib(path: Option<String>) -> Result<String> {
    let path = path.unwrap_or("./main.ts".to_string());
    Ok(std::fs::read_to_string(path)?)
}

pub fn exec_cli() -> Result<()> {
    let cli = Cli::parse();

    match cli.command {
        SubCommands::Run { path } => {
            compiler::jit(&path.unwrap())?

        }
        SubCommands::Runold { path } => {
            let contents = load_program(path)?;
            let ast = parse(&contents)?;
            let typed_program = type_ast(ast)?;
            let engine = generate_mlir(typed_program, false)?;
            unsafe { engine.invoke_packed("main", &mut [])? };

        }
        SubCommands::Build {
            emit_mlir: _,
            emit_llvmir,
            path,
            analyse,
        } => {

            let engine = if analyse {
                compiler::compile_with_analysis(&path.unwrap())?
            } else {
                compiler::compile(&path.unwrap())?
            };

            if emit_llvmir {
                engine.dump_to_object_file("testllvm.ir");
            }
        }
    }

    Ok(())
}
