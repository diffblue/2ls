int nondet();

void SimpleMultipleDep(int a, int b, int c, int d) {
    b = 0;
    a = 0;
      while (c >= b + 1) {
          if (d >= a + 1) {
            a = a + 1;
          }
          else if (a >= d) {
            a = 0;
            b = b + 1;
          }
          else
            return;
      }
          return;
}
