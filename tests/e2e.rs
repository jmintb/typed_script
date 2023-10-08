use anyhow::Result;
use assert_cmd::Command;
use rstest::rstest;
use std::path::PathBuf;

#[rstest]
fn test_well_formed_programs(#[files("./test_programs/*.ts")] path: PathBuf) -> Result<()> {
    let mut cmd = Command::cargo_bin("typed_script")?;
    let assert = cmd.arg("run").arg(path.clone()).assert();
    assert.success();
    insta::assert_snapshot!(
        format!(
            "test_well_formed_programs_{}",
            path.file_name().unwrap().to_str().unwrap()
        ),
        String::from_utf8(cmd.ok().unwrap().stdout)?
    );
    Ok(())
}

#[rstest]
fn snapshop_mlir_output(#[files("./test_programs/*.ts")] path: PathBuf) -> Result<()> {
    let mut cmd = Command::cargo_bin("typed_script")?;
    let assert = cmd
        .args(&["build", "--emit-mlir"])
        .arg(path.clone())
        .assert();
    assert.success();
    insta::assert_snapshot!(
        format!(
            "test_mlir_snapshot_{}",
            path.file_name().unwrap().to_str().unwrap()
        ),
        String::from_utf8(cmd.ok().unwrap().stdout)?
    );
    Ok(())
}

#[rstest]
fn snapshop_ast_output(#[files("./test_programs/*.ts")] path: PathBuf) -> Result<()> {
    let mut cmd = Command::cargo_bin("typed_script")?;
    let assert = cmd
        .args(&["build", "--emit-ast"])
        .arg(path.clone())
        .assert();
    assert.success();
    insta::assert_snapshot!(
        format!(
            "test_ast_snapshot_{}",
            path.file_name().unwrap().to_str().unwrap()
        ),
        String::from_utf8(cmd.ok().unwrap().stdout)?
    );
    Ok(())
}
