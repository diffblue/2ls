int nondet();

void speedpldi4(int a, int b) {
    if (0 >= a || a >= b) {
        return;
    }
    else if (b >= a + 1 && a >= 1) {
      while (b >= 1) {
          if (a >= b + 1) {
            b = b - 1;
          }
          else if (b >= a) {
            b = b - a;
          }
          else
            return;
      }
          return;
    }
    else
      return;
}
