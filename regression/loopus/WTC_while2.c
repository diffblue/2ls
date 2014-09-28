int nondet();

void while2(int a, int b, int c) {
    a = b;
      while (a >= 1) {
        c = b;
          while (1) {
            if (c >= 1) {
              c = c - 1;
            }
            else if (0 >= c) {
              a = a - 1;
                break;
            }
            else
              return;
          }
      }
          return;
}
