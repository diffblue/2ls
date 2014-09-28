int nondet();

void linear(int a) {
  if (a >= 1) {
    while (a >= 1) {
      a = a - 1;
    }
  }
  else if (a == 100) {
    a = 100;
    while (a >= 1) {
      a = a - 1;
    }
  }
  else
    return;
}
