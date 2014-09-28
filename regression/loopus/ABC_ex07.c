int nondet();

void ex07(int a, int b, int c, int d) {
    a = 1;
      while (b >= a) {
        c = 1;
          while (1) {
            if (d >= c) {
              c = c + 1;
            }
            else if (c >= d + 1) {
              a = a + 1;
                break;
            }
            else
              return;
          }
      }
          return;
}
