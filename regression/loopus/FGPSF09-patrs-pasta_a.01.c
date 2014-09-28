int nondet();

void a(int a, int b) {
    while (a >= 1) {
      b = 0;
        while (1) {
          if (a >= b + 1 && b >= 0 && a >= 1) {
            b = b + 1;
          }
          else if (b >= a && b >= 0 && a >= 1) {
            a = a - 1;
            break;
          }
          else
            return;
        }
    }
}
