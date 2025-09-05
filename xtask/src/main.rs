use std::env::{args, current_dir, set_current_dir};
use std::path::PathBuf;
use std::process;

type Error = Box<dyn std::error::Error>;

type Result<T> = std::result::Result<T, Error>;

fn main() -> Result<()> {
    let args: Vec<String> = args().collect();

    if args.len() < 2 {
        println!("please one of the following commands: [lint]");
        return Ok(());
    }

    let mut parent_dir: PathBuf = current_dir()?;

    set_current_dir(parent_dir)?;

    let command = &args[1];

    if command == "lint" {
        println!("linting project");
        process::Command::new("cargo")
            .args(["fmt", "--all"])
            .spawn()?
            .wait();

        process::Command::new("cargo")
            .args(["clippy", "--fix"])
            .spawn()?
            .wait();
    }
    Ok(())
}

fn print_help_message() {
    println!();
}
