fn main() {
  let a = 2;
  let b = 2;
  let c = 1;

  if (a) == (b) {
    print("a equals b \n", 12);     
  }

  if (a) == (c) {
    print("a equals c \n", 12);
  }

  if (a) != (c) {
    print("a not equal to c \n", 20);
  }

  if (a) > (c) {
    print("a greater than c \n", 18);
  }

  if (a) >= (c) {
    print("a greater than or equal to c \n", 30);
  }

  if (a) >= (a) {
    print("a greater than or equal to a \n", 30);
  }

  if (c) <= (a) {
    print("c less than or equal to a \n", 27);
  }

  if (a) <= (c) {
    print("a less than or equal to c \n", 27);
  }

  if (a) <= (a) {
    print("a less than or equal to a \n", 27);
  }

  if (c) < (a)  {
    print("c less than a \n", 18);
  }

  return
}
