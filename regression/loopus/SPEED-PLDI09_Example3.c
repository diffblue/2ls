int nondet();

void Example3(int a, int b, int c, int d, int e) {
    if (b >= a + 1 && a >= 1) {
      e = nondet();
      d = 0;
      c = 0;
        while (b >= d + 1) {
          e = nondet();
            if (0 >= e + 1 || e >= 1) {
              e = nondet();
              if (a >= c + 1) {
                e = nondet();
                c = c + 1;
              }
              else if (c >= a) {
                e = nondet();
                c = 0;
                d = d + 1;
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
        e = nondet();
            return;
    }
    else
        return;
}
