int nondet();

void insertsort(int a, int b, int c, int d, int e) {
    a = 1;
      while (b >= a + 1) {
        e = nondet();
          d = a - 1;
          c = e;
            while (1) {
              if (0 >= d + 1) {
                e = nondet();
                a = a + 1;
                  break;
              }
              else if (d >= 0) {
                e = nondet();
                if (e >= c + 1) {
                  e = nondet();
                  d = d - 1;
                }
                else if (c >= e) {
                  e = nondet();
                  a = a + 1;
                    break;
                }
                else
                  return;
              }
              else
                return;
            }
      }
      e = nondet();
          return;
}
