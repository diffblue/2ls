int nondet();

void ex03(int a, int b, int c, int d, int e) {
    a = 1;
      while (b >= a) {
        c = 1;
          while (1) {
            if (a >= c) {
              d = a + 1;
              while (1) {
                if (b >= d) {
                  e = 1;
                  while (1) {
                    if (d >= e) {
                      e = e + 1;
                    }
                    else if (e >= d + 1) {
                      d = d + 1;
                        break;
                    }
                    else
                      return;
                  }
                }
                else if (d >= b + 1) {
                  c = c + 1;
                    break;
                }
                else
                  return;
              }
            }
            else if (c >= a + 1) {
              a = a + 1;
              break;
            }
            else
              return;
          }
      }
          return;
}
