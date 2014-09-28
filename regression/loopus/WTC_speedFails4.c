int nondet();

void speedFails4(int a, int b, int c, int d) {
    if (a >= 1) {
      d = b;
      b = c;
      c = a;
      a = 1;
      while (b >= d) {
          if (c >= 1) {
            d = d + a;
          }
          else if (0 >= c) {
            d = d - a;
          }
          else
            return;
      }
          return;
    }
    else if (0 >= a) {
      d = b;
      b = c;
      c = a;
      a = -1;
      while (b >= d) {
          if (c >= 1) {
            d = d + a;
          }
          else if (0 >= c) {
            d = d - a;
          }
          else
            return;
      }
          return;
    }
    else
      return;
}
