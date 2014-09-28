int nondet();

void speedpldi2(int a, int b, int c) {
    if (a >= 0 && b >= 1) {
      c = a;
      a = b;
      b = 0;
      while (c >= 1 && a >= 0) {
          if (a >= b + 1) {
            b = b + 1;
            c = c - 1;
          }
          else if (b >= a) {
            b = 0;
          }
          else
            return;
      }
          return;
    }
    else if (0 >= a + 1 || 0 >= b) {
        return;
    }
    else
      return;
}
