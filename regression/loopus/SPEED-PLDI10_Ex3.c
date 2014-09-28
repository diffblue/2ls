int nondet();

void Ex3(int a, int b, int c, int d) {
      while (a >= 1) {
        d = nondet();
          b = d;
          c = a;
            while (1) {
              if (0 >= c) {
                d = nondet();
                a = c;
                break;
              }
              else if (c >= 1) {
                d = nondet();
                if (b >= d + 1 || d >= b + 1) {
                  d = nondet();
                  a = c;
                  break;
                }
                else if (1) {
                  c = c - 1;
                }
                else
                  return;
              }
              else
                return;
            }
      }
      d = nondet();
          return;
}
