int nondet();

void aa_15(int a, int b) {
    while (1) {
      if (a + b >= 1 && a >= 1) {
        a = a - 1;
      }
      else if (0 >= a && a + b >= 1 && b >= 1) {
        b = b - 1;
      }
      else if (0 >= b && 0 >= a && a + b >= 1) {
      }
      else
        return;
    }
}
