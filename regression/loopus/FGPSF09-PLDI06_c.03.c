int nondet();

void c(int a, int b, int c) {
    while (1) {
      if (a >= b + 1 && c >= b + 1) {
        b = b + 1;
      }
      else if (a >= b + 1 && b >= c) {
        c = c + 1;
      }
      else
        return;
    }
}
