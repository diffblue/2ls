int nondet();

void complete3(int a, int b) {
    while (a >= 0) {
      b = 0;
        while (1) {
          if (a >= 1 + b) {
            b = b + 1;
          }
          else if (b >= a) {
            a = a - 1;
            break;
          }
          else
            return;
        }
    }
}
