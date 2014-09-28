int nondet();

void poly2(int a, int b, int c) {
    while (1) {
      if (a >= 0) {
        a = a + b;
        b = b - 2;
        c = c + 1;
      }
      else if (a >= 0) {
        a = a + c;
        c = c - 2;
      }
      else
        return;
    }
}
