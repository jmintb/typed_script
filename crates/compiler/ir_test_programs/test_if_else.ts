fn main() {
  let test_val = "some str"; 

  if (1) > (0) {
    borrow_val(test_val);
    move_val(test_val);
  } else {
    borrow_val(test_val);
    move_val(test_val);
  }
  return;
}

fn borrow_val(val: str) {
  return;  
}

fn move_val(owned val: str) {
  return;
}
