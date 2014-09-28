int nondet();

void sect5_sumSum(int a, int b, int c, int d) {
  a = 0;
    while (b >= 1) {
      d = 0;
      c = 0;
        while (1) {
          if (b >= c + 1) {
            d = d + c;
            c = c + 1;
          }
          else if (c >= b) {
            b = b - 1;
            a = a + d;
            break;
          }
          else
            return;
        }
    }
}
