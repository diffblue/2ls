int nondet();

void Ex5(int a, int b, int c, int d, int e, int f) {
    b = a;
    a = 0;
      while (b >= a + 1) {
        f = nondet();
        d = b;
        c = 0;
          while (1) {
            if (0 >= f + 1 || f >= 1) {
              f = nondet();
              if (0 >= f + 1 || (0 >= f + 1 && f >= 1) || f >= 1) {
                e = d - 1;
                f = nondet();
                c = 1;
                d = e;
              }
              else if (0 >= 1 || 0 >= 1) {
                f = nondet();
                d = d - 1;
              }
              else if (0 >= 1 || 0 >= 1) {
                f = nondet();
                e = d;
                c = 1;
                d = e;
              }
              else if (1) {
              }
              else
                return;
            }
            else if (1) {
              if (c == 0) {
                b = d;
                f = nondet();
                a = a + 1;
                break;
              }
              else if (0 >= c + 1 || c >= 1) {
                f = nondet();
                b = d;
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
