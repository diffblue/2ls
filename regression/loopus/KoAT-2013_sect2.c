int nondet();

void sect2(int a, int b, int c, int d) {
  a = 0;
    while (b >= 1) {
      a = a + 1;
      b = b - 1;
    }
    c = a;
      while (c >= 1) {
        d = c;
          while (1) {
            if (c >= 1 && d >= 1) {
              d = d - 1;
            }
            else if (0 >= d && c >= 1) {
              c = c - 1;
              break;
            }
            else
              return;
          }
      }
}
