int nondet();

void realshellsort(int a, int b, int c, int d, int e, int f) {
    if (a == 0) {
      f = nondet();
      b = 0;
      while (b >= 1) {
        c = 0;
        f = nondet();
          while (1) {
            if (a >= c + 1) {
              f = nondet();
              e = c;
              d = f;
                while (1) {
                  if (b >= e + 1) {
                    f = nondet();
                    c = c + 1;
                      break;
                  }
                  else if (e >= b) {
                    f = nondet();
                    if (f >= d + 1) {
                      f = nondet();
                      e = e - b;
                    }
                    else if (d >= f) {
                      f = nondet();
                      c = c + 1;
                        break;
                    }
                    else
                      return;
                  }
                  else
                    return;
                }
            }
            else if (c >= a) {
              f = nondet();
              if (b == 0) {
                f = nondet();
                b = 0;
                break;
              }
              else if ((1 + 2*f >= b && f >= 0 && b >= 2*f && b >= 1) || (2*f >= b && 0 >= f && 1 + b >= 2*f && 0 >= b + 1)) {
                b = f;
                f = nondet();
                break;
              }
              else
                return;
            }
            else
              return;
          }
      }
      f = nondet();
          return;
    }
    else if ((a >= 2*f && 1 + 2*f >= a && f >= 0 && a >= 1) || (0 >= a + 1 && 0 >= f && 2*f >= a && 1 + a >= 2*f)) {
      b = f;
      f = nondet();
      while (b >= 1) {
        c = 0;
        f = nondet();
          while (1) {
            if (a >= c + 1) {
              f = nondet();
              e = c;
              d = f;
                while (1) {
                  if (b >= e + 1) {
                    f = nondet();
                    c = c + 1;
                      break;
                  }
                  else if (e >= b) {
                    f = nondet();
                    if (f >= d + 1) {
                      f = nondet();
                      e = e - b;
                    }
                    else if (d >= f) {
                      f = nondet();
                      c = c + 1;
                        break;
                    }
                    else
                      return;
                  }
                  else
                    return;
                }
            }
            else if (c >= a) {
              f = nondet();
              if (b == 0) {
                f = nondet();
                b = 0;
                break;
              }
              else if ((1 + 2*f >= b && f >= 0 && b >= 2*f && b >= 1) || (2*f >= b && 0 >= f && 1 + b >= 2*f && 0 >= b + 1)) {
                b = f;
                f = nondet();
                break;
              }
              else
                return;
            }
            else
              return;
          }
      }
      f = nondet();
          return;
    }
    else
      return;
}
