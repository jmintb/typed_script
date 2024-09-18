use anyhow::Result;
use fusion::cli::exec_cli;

fn main() -> Result<()> {
    exec_cli()

    // let program = "fn main () {
    //         printf(\"hello\");
    //      }";

    // let ast = parse(program).unwrap();
    // let engine = generate_mlir(ast).unwrap();

    // // println!("module {:?}", module.as_operation());
    // let mut result: i32 = 4;

    // let mut val = std::ffi::CString::new("jj").unwrap();

    // let mut ptr = val.as_ptr();

    // // let engine = ExecutionEngine::new(&module, 0, &[], true);

    // engine.dump_to_object_file("llvmtest.ir");

    // unsafe {
    //     engine
    //         .invoke_packed(
    //             "main",
    //             &mut [ptr as *mut (), &mut result as *mut i32 as *mut ()],
    //         )
    //         .unwrap();
    // };
}
