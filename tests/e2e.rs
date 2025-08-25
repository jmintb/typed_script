use anyhow::Result;
use assert_cmd::Command;
use rstest::rstest;
use std::path::PathBuf;

#[rstest]
fn test_well_formed_programs(#[files("./ir_test_programs/test_*.ts")] path: PathBuf) -> Result<()> {
    let mut cmd = Command::cargo_bin("fusion")?;
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
fn snapshop_mlir_output(#[files("./ir_test_programs/test_*.ts")] path: PathBuf) -> Result<()> {
    let mut cmd = Command::cargo_bin("fusion")?;
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
