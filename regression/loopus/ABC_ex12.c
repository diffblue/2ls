int nondet();

void ex12(int a, int b, int c) {
      while (b >= 1) {
        c = a;
          while (1) {
            if (c >= a) {
              c = c - 1;
            }
            else if (a >= c + 1) {
              b = b - 1;
                break;
            }
            else
              return;
          }
      }
          return;
}
