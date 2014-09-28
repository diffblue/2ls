int nondet();

void ex3(int a, int b, int c, int d, int e, int f, int g) {
    a = b;
      while (b >= 2) {
        g = nondet();
          c = b - 1;
          d = a + b - 1;
            while (1) {
              if (c >= d) {
                g = nondet();
                a = d - c + 1;
                b = c - 1;
                  break;
              }
              else if (d >= c + 1) {
                g = nondet();
                if (0 >= g + 1 || g >= 1) {
                  g = nondet();
                  f = d - 1;
                  e = c;
                      d = f - 1;
                      c = e;
                }
                else if (1) {
                  a = d - c + 1;
                  b = c - 1;
                    break;
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
