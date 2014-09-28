int nondet();

void SimpleMultiple(int a, int b, int c, int d) {
    a = 0;
    b = 0;
      while (c >= b + 1) {
          if (d >= a + 1) {
            a = a + 1;
          }
          else if (a >= d) {
            b = b + 1;
          }
          else
            return;
      }
          return;
}
