int nondet();

void Example1(int a, int b, int c, int d, int e) {
    a = 0;
      while (b >= a + 1) {
        e = nondet();
          c = 0;
          d = a + 1;
            while (1) {
              if (d >= b) {
                e = nondet();
                if (c >= 1) {
                  a = d - 1;
                  e = nondet();
                  break;
                }
                else if (0 >= c) {
                  e = nondet();
                  a = d;
                  break;
                }
                else
                  return;
              }
              else if (b >= d + 1) {
                e = nondet();
                if (0 >= e + 1 || e >= 1) {
                  e = nondet();
                  c = c + 1;
                  d = d + 1;
                }
                else if (1) {
                  if (c >= 1) {
                    a = d - 1;
                    e = nondet();
                    break;
                  }
                  else if (0 >= c) {
                    e = nondet();
                    a = d;
                    break;
                  }
                  else
                    return;
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
