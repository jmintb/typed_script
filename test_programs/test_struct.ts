struct Test {
  fielda: string,
  fieldb: string,
  fie: integer,
}

struct String {
  val: string,
  len: integer,
}

fn new_string(val: string, len: integer) -> String {
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
