int nondet();

void random2d(int a, int b, int c, int d, int e) {
    a = 0;
      while (b >= a + 1) {
        e = nondet();
          if (3 >= e && e >= 0) {
            d = e;
            e = nondet();
            c = a + 1;
              if (1 >= d) {
                e = nondet();
                if (0 >= d) {
                  e = nondet();
                  if (d == 0) {
                    e = nondet();
                    a = c;
                  }
                  else if (0 >= d + 1 || d >= 1) {
                    e = nondet();
                    a = c;
                  }
                  else
                    return;
                }
                else if (d >= 1) {
                  e = nondet();
                  if (d == 1) {
                    e = nondet();
                    a = c;
                  }
                  else if (0 >= d || d >= 2) {
                    e = nondet();
                    a = c;
                  }
                  else
                    return;
                }
                else
                  return;
              }
              else if (d >= 2) {
                e = nondet();
                if (2 >= d) {
                  e = nondet();
                  if (d == 2) {
                    e = nondet();
                    a = c;
                  }
                  else if (1 >= d || d >= 3) {
                    e = nondet();
                    a = c;
                  }
                  else
                    return;
                }
                else if (d >= 3) {
                  e = nondet();
                  if (d == 3) {
                    e = nondet();
                    a = c;
                  }
                  else if (2 >= d || d >= 4) {
                    e = nondet();
                    a = c;
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
          else if (0 >= e + 1 || e >= 4) {
            e = nondet();
            a = a + 1;
          }
          else
            return;
      }
      e = nondet();
          return;
}
