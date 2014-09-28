int nondet();

void realselect(int a, int b, int c, int d, int e) {
    a = 0;
      while (b >= 2 + a) {
        e = nondet();
        d = nondet();
          c = a + 1;
            while (1) {
              if (b >= c + 1) {
                d = nondet();
                e = nondet();
                if (d >= e + 1 || e >= d) {
                  e = nondet();
                  c = c + 1;
                  d = nondet();
                }
                else
                    return;
              }
              else if (c >= b) {
                d = nondet();
                e = nondet();
                a = a + 1;
                  break;
              }
              else
                return;
            }
      }
      e = nondet();
      d = nondet();
          return;
}
