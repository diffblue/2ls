int nondet();

void c(int a, int b) {
    while (1) {
      if ((a >= b + 1 && b >= 1 && a >= 1) || (a >= b + 1 && b >= a + 1 && b >= 1 && a >= 1)) {
        a = a - b;
      }
      else if ((a >= b + 1 && b >= a && b >= 1 && a >= 1) || (b >= a + 1 && b >= a && b >= 1 && a >= 1)) {
        b = b - a;
      }
      else
        return;
    }
}
