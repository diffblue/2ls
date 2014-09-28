int nondet();

void cousot9(int a, int b, int c, int d) {
    b = c;
    a = d;
      while (b >= 1) {
        d = nondet();
          if (a >= 1) {
            d = nondet();
            a = a - 1;
          }
          else if (0 >= a) {
            d = nondet();
            a = c;
            b = b - 1;
          }
          else
            return;
      }
      d = nondet();
          return;
}
