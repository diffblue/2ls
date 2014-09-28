int nondet();

void ex2(int a, int b, int c, int d, int e) {
    a = b;
      while (b >= 2) {
        e = nondet();
          d = a + b - 1;
          c = b - 1;
            while (1) {
              if (c >= d + 1) {
                e = nondet();
                b = c - 1;
                a = d - c + 1;
                  break;
              }
              else if (d >= c) {
                e = nondet();
                if (0 >= e + 1 || e >= 1) {
                  e = nondet();
                  d = d - 1;
                }
                else if (1) {
                  b = c - 1;
                  a = d - c + 1;
                    break;
                }
                else
                  return;
              }
              else
                return;
            }
      }
      e = nondet();
          return;
}
