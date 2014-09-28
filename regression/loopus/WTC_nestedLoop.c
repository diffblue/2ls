int nondet();

void nestedLoop(int a, int b, int c, int d, int e, int f, int g, int h) {
    if (c >= 0 && b >= 0 && a >= 0) {
      d = 0;
      while (a >= d + 1) {
        e = 0;
        f = d;
          while (1) {
            if (b >= e + 1) {
              g = e + 1;
              h = f;
                while (1) {
                  if (c >= h + 1) {
                    h = h + 1;
                  }
                  else if (h >= c) {
                    e = g;
                    f = h;
                    break;
                  }
                  else
                    return;
                }
            }
            else if (e >= b) {
              d = f + 1;
                break;
            }
            else
              return;
          }
      }
          return;
    }
    else if (0 >= a + 1 || 0 >= b + 1 || 0 >= c + 1) {
        return;
    }
    else
      return;
}
