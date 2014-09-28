int nondet();

void aa_17(int a, int b) {
    while (1) {
      if ((a >= b + 1 && a + b >= 1) || (2*a >= 1 && b == a)) {
        a = a - 1;
      }
      else if ((b >= a + 1 && a + b >= 1 && b >= a) || (a >= b + 1 && a + b >= 1 && b >= a)) {
        b = b - 1;
      }
      else
        return;
    }
}
