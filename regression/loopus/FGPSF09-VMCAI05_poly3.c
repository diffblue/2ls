int nondet();

void poly3(int a, int b, int c) {
    while (1) {
      if (b*b*b >= c && a >= 0) {
        a = a - 1;
        c = c - 1;
      }
      else if (b*b*b >= c && a >= 0) {
        b = b + c;
        c = c - 1;
      }
      else
        return;
    }
}
