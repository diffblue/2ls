int nondet();

void perfect(int a, int b, int c, int d) {
    if (1 >= a) {
        return;
    }
    else if (a >= 2) {
      b = a;
      c = a - 1;
        while (c >= 1) {
          d = a;
            while (1) {
              if (d >= c && c >= 1) {
                d = d - c;
              }
              else if (c >= d + 1) {
                if (d == 0) {
                  b = b - c;
                  c = c - 1;
                  break;
                }
                else if (0 >= d + 1 || d >= 1) {
                  c = c - 1;
                  break;
                }
                else
                  return;
              }
              else
                return;
            }
        }
        a = b;
          if (0 >= a + 1 || a >= 1 || a == 0) {
                return;
          }
          else
              return;
    }
    else
      return;
}
