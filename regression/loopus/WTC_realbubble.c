int nondet();

void realbubble(int a, int b, int c, int d, int e, int f) {
    a = a - 1;
      while (a >= 1) {
        c = 0;
        b = 0;
        e = nondet();
        f = nondet();
          while (1) {
            if (a >= b + 1) {
              f = nondet();
              e = nondet();
              if (e >= f + 1) {
                f = nondet();
                e = nondet();
                d = 1;
                  b = b + 1;
                  c = d;
              }
              else if (f >= e) {
                e = nondet();
                d = c;
                f = nondet();
                b = b + 1;
                c = d;
              }
              else
                return;
            }
            else if (b >= a) {
              e = nondet();
              f = nondet();
              if (c == 0) {
                e = nondet();
                f = nondet();
                  return;
              }
              else if (0 >= c + 1 || c >= 1) {
                f = nondet();
                e = nondet();
                a = a - 1;
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
      f = nondet();
          return;
}
