int nondet();

void sipmabubble(int a, int b, int c, int d) {
      while (a >= 0) {
        d = nondet();
        b = 0;
        c = nondet();
          while (1) {
            if (a >= 1 + b) {
              d = nondet();
              c = nondet();
              if (c >= d + 1) {
                d = nondet();
                c = nondet();
                  b = b + 1;
              }
              else if (d >= c) {
                d = nondet();
                c = nondet();
                b = b + 1;
              }
              else
                return;
            }
            else if (b >= a) {
              c = nondet();
              d = nondet();
              a = a - 1;
                break;
            }
            else
              return;
          }
      }
      c = nondet();
      d = nondet();
          return;
}
