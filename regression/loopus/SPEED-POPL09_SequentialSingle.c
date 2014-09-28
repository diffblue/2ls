int nondet();

void SequentialSingle(int a, int b, int c) {
    a = 0;
      while (b >= a + 1) {
        c = nondet();
          if (0 >= c + 1 || c >= 1) {
            c = nondet();
            a = a + 1;
          }
          else if (1) {
            while (b >= a + 1) {
              c = nondet();
                a = a + 1;
            }
            c = nondet();
                return;
          }
          else
            return;
      }
      c = nondet();
        while (b >= a + 1) {
          c = nondet();
            a = a + 1;
        }
        c = nondet();
            return;
}
