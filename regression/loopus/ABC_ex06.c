int nondet();

void ex06(int a, int b, int c) {
    a = 1;
      while (b >= a) {
        c = a;
          while (1) {
            if (b >= c) {
              c = c + 1;
            }
            else if (c >= b + 1) {
              a = a + 1;
                break;
            }
            else
              return;
          }
      }
          return;
}
