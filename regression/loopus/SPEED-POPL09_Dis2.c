int nondet();

void Dis2(int a, int b, int c) {
      while (a >= c + 1) {
          if (b >= c + 1) {
            c = c + 1;
          }
          else if (c >= b) {
            b = b + 1;
          }
          else
            return;
      }
          return;
}
