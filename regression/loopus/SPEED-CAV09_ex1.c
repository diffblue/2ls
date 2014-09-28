int nondet();

void ex1(int a, int b, int c) {
    a = 0;
    b = 0;
      while (99 >= b) {
          if (c >= a + 1) {
            a = a + 1;
          }
          else if (a >= c) {
            b = b + 1;
          }
          else
            return;
      }
          return;
}
