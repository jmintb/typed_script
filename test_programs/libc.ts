fn fdopen(fd: int, mode: String);
fn fclose(fd, mode);
fn fwrite(val, size, len, file);

pub fn print(val: String) {
    let stdoutptr = fdopen(1, "w");
    fwrite(val, len(val));
}

fn main() {
  
}
