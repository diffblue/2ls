int nondet();

void aaron2(int a, int b, int c, int d) {
    if (a >= 0) {
      int tmp0 = c;
      c = b;
      b = tmp0;
      d = nondet();
      while (c >= b && a >= 0) {
        d = nondet();
          if (0 >= d + 1 || d >= 1) {
            d = nondet();
            c = c - a - 1;
          }
          else if (1) {
            b = b + a + 1;
          }
          else
            return;
      }
      d = nondet();
          return;
    }
    else if (0 >= a + 1) {
      d = nondet();
        return;
    }
    else
      return;
}
