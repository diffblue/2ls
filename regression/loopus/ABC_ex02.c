int nondet();

void ex02(int a, int b, int c) {
    a = 0;
      while (b >= 1 + a) {
        c = 0;
          while (1) {
            if (a >= c) {
              c = c + 1;
            }
            else if (c >= a + 1) {
              a = a + 1;
                break;
            }
            else if (1) {
              c = 1;
              a = 1;
              b = 1;
              break;
            }
            else
              return;
          }
      }
          return;
}
