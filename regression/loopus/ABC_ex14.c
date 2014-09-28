int nondet();

void ex14(int a, int b, int c, int d, int e) {
      while (b >= 1) {
        c = 1;
          while (1) {
            if (a >= c) {
              d = b;
              while (1) {
                if (b + c >= d) {
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
                else if (d >= b + c + 1) {
                  c = c + 1;
                    break;
                }
                else
                  return;
              }
            }
            else if (c >= a + 1) {
              b = b - 1;
                break;
            }
            else
              return;
          }
      }
          return;
}
