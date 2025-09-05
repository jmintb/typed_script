//! This crate hosts adhoc scripts using the [xtask](https://github.com/matklad/cargo-xtask)
//! pattern.
//! Think of it as an alternative to makefile or just, using cargo and rust.
//!
//! This allows us to write custom tooling for working with the Fusion project without relying on
//! external tools. We also get to write the tools in rust instead of bash or similar. Making
//! this crossplatform and easier to maintain.
//!
//! The strategy is to keep this is simple as possible with next to no external dependencies.
//! As the requirements grow we can grow the crate a long with it.
//!
//! Current it only houses commands for performing code quality checks.

use std::env::args;
use std::process;

type Error = Box<dyn std::error::Error>;
type Result<T> = std::result::Result<T, Error>;

fn main() -> Result<()> {
    let args: Vec<String> = args().collect();

    if args.len() < 2 {
        println!("please provide one of the following commands: [check, fix]");
        return Ok(());
    }

    let command = &args[1];

    if command == "check" {
        run_code_checks()?;
    } else if command == "fix" {
        run_code_checks_and_apply_fixes()?;
    }

    Ok(())
}

fn run_code_checks() -> Result<()> {
    println!("Running code quality checks!");

    println!("Running rustfmt");
    process::Command::new("cargo")
        .args(["fmt", "--all", "--check"])
        .spawn()?
        .wait()?;

    println!("Running clippy");
    process::Command::new("cargo")
        .args(["clippy"])
        .spawn()?
        .wait()?;

    println!("Running cargo check");
    process::Command::new("cargo")
        .args(["check", "--workspace", "--all-targets", "--all-features"])
        .spawn()?
        .wait()?;

    Ok(())
}

fn run_code_checks_and_apply_fixes() -> Result<()> {
    println!("Applying code quality fixes!");

    println!("Running rustfmt");
    process::Command::new("cargo")
        .args(["fmt", "--all"])
        .spawn()?
        .wait()?;

    println!("Running clippy");
    process::Command::new("cargo")
        .args(["clippy", "--fix", "--allow-dirty"])
        .spawn()?
        .wait()?;

    println!("Running cargo fix");
    process::Command::new("cargo")
        .args([
            "fix",
            "--workspace",
            "--all-targets",
            "--all-features",
            "--allow-dirty",
        ])
        .spawn()?
        .wait()?;

    Ok(())
}
