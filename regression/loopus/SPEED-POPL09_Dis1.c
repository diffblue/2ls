int nondet();

void Dis1(int a, int b, int c, int d) {
      while (a >= b + 1) {
          if (c >= d + 1) {
            d = d + 1;
          }
          else if (d >= c) {
            b = b + 1;
          }
          else
            return;
      }
          return;
}
