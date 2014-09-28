int nondet();

void Example6(int a, int b, int c, int d, int e, int f, int g, int h) {
    a = 0;
    b = 0;
    c = 0;
      while (d >= c + 1) {
        e = c + 1;
        h = nondet();
          if (0 >= h + 1 || h >= 1) {
            h = nondet();
            f = b;
            while (1) {
              if (f >= g) {
                c = e;
                b = f + 1;
                h = nondet();
                break;
              }
              else if (g >= f + 1) {
                f = f + 1;
                h = nondet();
              }
              else
                return;
            }
          }
          else if (1) {
            f = a;
            while (1) {
              if (f >= g) {
                a = f + 1;
                c = e;
                h = nondet();
                break;
              }
              else if (g >= f + 1) {
                h = nondet();
                f = f + 1;
              }
              else
                return;
            }
          }
          else
            return;
      }
      h = nondet();
          return;
}
