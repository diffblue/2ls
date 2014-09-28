int nondet();

void NestedSingle(int a, int b, int c, int d) {
    a = 0;
      while (b >= a + 1) {
        c = a;
        d = nondet();
          while (1) {
            if (c >= b) {
              d = nondet();
              a = c + 1;
                break;
            }
            else if (b >= c + 1) {
              d = nondet();
              if (0 >= d + 1 || d >= 1) {
                d = nondet();
                c = c + 1;
              }
              else if (1) {
                a = c + 1;
                  break;
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
