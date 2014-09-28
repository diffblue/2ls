int nondet();

void NestedLoop(int a, int b, int c, int d, int e, int f, int g, int h, int i) {
    if (c >= 0 && b >= 0 && a >= 0) {
      d = 0;
      i = nondet();
        while (a >= d + 1) {
          i = nondet();
            if (0 >= i + 1 || i >= 1) {
              f = d;
              i = nondet();
              e = 0;
              while (1) {
                if (e >= b) {
                  i = nondet();
                  d = f + 1;
                    break;
                }
                else if (b >= e + 1) {
                  i = nondet();
                  if (0 >= i + 1 || i >= 1) {
                    i = nondet();
                    h = f;
                    g = e + 1;
                      while (1) {
                        if (h >= c) {
                          e = g;
                          f = h;
                          i = nondet();
                          break;
                        }
                        else if (c >= h + 1) {
                          i = nondet();
                          if (0 >= i + 1 || i >= 1) {
                            i = nondet();
                            h = h + 1;
                          }
                          else if (1) {
                            f = h;
                            e = g;
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
                    d = f + 1;
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
                return;
            }
            else
              return;
        }
        i = nondet();
            return;
    }
    else
        return;
}
