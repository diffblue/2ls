int nondet();

void rsd(int a, int b, int c, int d) {
    if (a >= 0) {
      d = nondet();
      c = 2*a;
      b = 2*a;
        while (c >= a) {
          d = nondet();
            if (0 >= d + 1 || d >= 1) {
              d = nondet();
              c = c - 1;
            }
            else if (1) {
              c = b - 1;
              b = b - 1;
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
