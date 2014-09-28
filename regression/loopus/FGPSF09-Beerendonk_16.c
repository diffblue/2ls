int nondet();

void aa_16(int a, int b, int c) {
    while (1) {
      if (c >= 0 && a + b >= c + 1 && a >= 1) {
        a = a - 1;
      }
      else if (0 >= a && c >= 0 && a + b >= c + 1 && b >= 1) {
        b = b - 1;
      }
      else if (0 >= b && 0 >= a && c >= 0 && a + b >= c + 1) {
      }
      else
        return;
    }
}
