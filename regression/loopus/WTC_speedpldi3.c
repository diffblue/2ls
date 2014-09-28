int nondet();

void speedpldi3(int a, int b, int c, int d) {
    if (0 >= a || a >= b) {
        return;
    }
    else if (b >= a + 1 && a >= 1) {
      c = 0;
      d = 0;
      while (b >= d + 1) {
          if (a >= c + 1) {
            c = c + 1;
          }
          else if (c >= a) {
            d = d + 1;
            c = 0;
          }
          else
            return;
      }
          return;
    }
    else
      return;
}
