int nondet();

void Ex1(int a, int b, int c, int d, int e) {
    b = a;
    a = 0;
      while (b >= a + 1) {
        e = nondet();
          d = b;
          c = a + 1;
            while (1) {
              if (d >= c + 1) {
                e = nondet();
                if (0 >= e + 1 || (0 >= e + 1 && e >= 1) || e >= 1) {
                  d = d - 1;
                  e = nondet();
                }
                else if (0 >= 1 || 0 >= 1) {
                  e = nondet();
                }
                else if (0 >= 1 || 0 >= 1) {
                  d = d - 1;
                  e = nondet();
                  c = c + 1;
                }
                else if (1) {
                  c = c + 1;
                }
                else
                  return;
              }
              else if (c >= d) {
                e = nondet();
                b = d;
                a = a + 1;
                  break;
              }
              else
                return;
            }
      }
      e = nondet();
          return;
}
