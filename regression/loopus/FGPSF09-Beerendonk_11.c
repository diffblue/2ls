int nondet();

void aa_11(int a, int b) {
    while (1) {
      if ((0 >= a && b == 1) || (b >= a + 1 && 1 + b >= 0 && b >= 1)) {
        b = a;
      }
      else if (b == 1 && a >= 1) {
        b = 0;
      }
      else if (1 + b >= 0 && a >= b && b >= 1) {
        b = b - 1;
      }
      else
        return;
    }
}
