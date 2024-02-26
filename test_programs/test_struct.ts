

struct Test {
  fielda: str,
  fieldb: str,
  fie: integer,
}

struct String {
  val: ptr,
  len: integer,
}

fn new_string(val: str, len: integer) -> String {
  return String { val, len} 
}

fn print_string(str: String) {
  print(str.val, str.len) 
  return
}

fn main() {
  let str = new_string("ac \n", 4);
  print_string(str)

  return;
}
