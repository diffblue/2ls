int nondet();

void c(int a, int b) {
    while (a >= 0) {
      b = 1;
        while (1) {
          if (a >= b + 1 && a >= 0 && b >= 1) {
            b = 2*b;
          }
          else if (b >= a && a >= 0 && b >= 1) {
            a = a - 1;
            break;
          }
          else
            return;
        }
    }
}
