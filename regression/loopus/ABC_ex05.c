int nondet();

void ex05(int a, int b, int c) {
    a = 1;
      while (b >= a) {
        c = 1;
          while (1) {
            if (a >= c) {
              c = c + 1;
            }
            else if (c >= a + 1) {
              a = a + 1;
                break;
            }
            else
              return;
          }
      }
          return;
}
