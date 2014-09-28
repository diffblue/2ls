int nondet();

void Example4(int a, int b, int c) {
    if (b >= a + 1 && a >= 1) {
      int tmp0 = a;
      c = nondet();
      a = b;
      b = tmp0;
        while (a >= 1) {
          c = nondet();
            if (0 >= c + 1 || c >= 1) {
              c = nondet();
              if (b >= a + 1) {
                c = nondet();
                a = a + 1;
              }
              else if (a >= b) {
                c = nondet();
                a = a - b;
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
        c = nondet();
            return;
    }
    else
        return;
}
