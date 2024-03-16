fn main() {
  let test_val = "some str"; 

  if (1) > (0) {
    borrow_val(test_val);
    move_val(test_val);
  } else {
    move_val(test_val);
    borrow_val(test_val);
  }
}

fn borrow_val(val: str) {
  
}

fn move_val(owned val: str) {
  
}
