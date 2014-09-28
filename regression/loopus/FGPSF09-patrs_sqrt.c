int nondet();

void aa_sqrt(int a, int b, int c, int d) {
  b = 1;
  c = 1;
  a = 0;
    while (d >= c && b >= 0) {
      a = a + 1;
      c = c + b + 2;
      b = b + 2;
    }
      return;
}
