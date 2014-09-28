int nondet();

void Example2(int a, int b, int c, int d) {
    if (b >= 1 && a >= 1) {
      d = nondet();
      c = 0;
        while (b >= 1) {
          d = nondet();
            if (0 >= d + 1 || d >= 1) {
              d = nondet();
              if (a >= c + 1) {
                d = nondet();
                c = c + 1;
                b = b - 1;
              }
              else if (c >= a) {
                c = 0;
                d = nondet();
              }
              else
                return;
            }
            else if (1) {
                return;
            }
            else
              return;
        }
        d = nondet();
            return;
    }
    else
        return;
}
