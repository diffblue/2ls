int nondet();

void cyclic(int a, int b, int c, int d) {
    if (b >= a + 1 && a >= 0) {
      c = a + 1;
      d = nondet();
        while (a >= c + 1 || c >= a + 1) {
          d = nondet();
            if (0 >= d + 1 || d >= 1) {
              d = nondet();
              if (b >= c) {
                c = c + 1;
                d = nondet();
              }
              else if (c >= b + 1) {
                c = 0;
                d = nondet();
              }
              else
                return;
            }
            else if (1) {
                return;
            }
            else
              return;
        }
        d = nondet();
            return;
    }
    else
        return;
}
