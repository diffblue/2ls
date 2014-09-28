int nondet();

void c(int a, int b) {
    while (a >= 0) {
      a = a + 1;
      b = 1;
        while (1) {
          if (a >= b && a >= 0 && b >= 1) {
            b = b + 1;
          }
          else if (b >= a + 1 && a >= 0 && b >= 1) {
            a = a - 2;
            break;
          }
          else
            return;
        }
    }
}
