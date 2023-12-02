fn fdopen(fd: int, mode: string) -> ptr;
fn fclose(fd, mode);
fn fwrite(val, size, len, file) -> int;


fn main() {
    let stdoutptr = fdopen(1, "w");
    fwrite("hello world with out printf!!!!", 4, 10, stdoutptr);
}
