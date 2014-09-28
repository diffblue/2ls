int nondet();

void counterex1b(int a, int b, int c, int d, int e, int f, int g) {
    int tmp0 = a;
    a = b;
    b = tmp0;
evalfbb8in: 
      while (b >= 0) {
        c = a;
        g = nondet();
          while (1) {
            if (0 >= c + 1) {
              g = nondet();
              e = c;
              d = b - 1;
                while (1) {
                  if (e >= f + 1) {
                    a = e;
                    b = d;
                    g = nondet();
                    goto evalfbb8in;
                  }
                  else if (f >= e) {
                    g = nondet();
                    if (0 >= g + 1 || g >= 1) {
                      g = nondet();
                      e = e + 1;
                    }
                    else if (1) {
                      b = d;
                      a = e;
                      goto evalfbb8in;
                    }
                    else
                      return;
                  }
                  else
                    return;
                }
            }
            else if (c >= 0) {
              g = nondet();
              if (0 >= g + 1 || g >= 1) {
                g = nondet();
                c = c - 1;
              }
              else if (1) {
                e = c;
                d = b - 1;
                  while (1) {
                    if (e >= f + 1) {
                      a = e;
                      b = d;
                      g = nondet();
                      goto evalfbb8in;
                    }
                    else if (f >= e) {
                      g = nondet();
                      if (0 >= g + 1 || g >= 1) {
                        g = nondet();
                        e = e + 1;
                      }
                      else if (1) {
                        b = d;
                        a = e;
                        goto evalfbb8in;
                      }
                      else
                        return;
                    }
                    else
                      return;
                  }
              }
              else
                return;
            }
            else
              return;
          }
      }
      g = nondet();
          return;
}
