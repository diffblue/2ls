int nondet();

void ex1(int a, int b, int c, int d, int e, int f) {
    c = 0;
    a = b;
      while (c >= 0 && a >= 0) {
        f = nondet();
          if (0 >= f + 1 || f >= 1) {
            d = c;
            f = nondet();
            while (1) {
              if (d >= b + 1) {
                f = nondet();
                e = d;
                d = a - 1;
                  c = e - 1;
                  a = d;
                    break;
              }
              else if (b >= d) {
                f = nondet();
                if (0 >= f + 1 || f >= 1) {
                  f = nondet();
                  d = d + 1;
                }
                else if (1) {
                  e = d;
                  d = a - 1;
                    c = e - 1;
                    a = d;
                      break;
                }
                else
                  return;
              }
              else
                return;
            }
          }
          else if (1) {
            e = c;
            d = a;
            c = e - 1;
            a = d;
              break;
          }
          else
            return;
      }
      f = nondet();
          return;
}
