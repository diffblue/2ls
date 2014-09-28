int nondet();

void c(int a, int b, int c) {
  if (a >= 1) {
      while (1) {
        if (a >= b + 1 && c >= a + 1 && a >= 1) {
          b = b + a;
        }
        else if (a >= b + 1 && c >= a + 1 && a >= 1) {
          c = b - a;
        }
        else
          return;
      }
  }
  else
      return;
}
