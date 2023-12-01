fn fdopen(fd: int, mode: String);
fn fclose(fd, mode);
fn fwrite(val, size, len, file);


fn main() {
    let stdoutptr = fdopen(1, "w");
    fwrite("hello world with out printf!!!!", 4, 10, stdoutptr);
}
