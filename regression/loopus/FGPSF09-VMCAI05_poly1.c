int nondet();

void poly1(int a, int b, int c) {
    while (1) {
      if (a >= b) {
        b = b + a;
        a = a + 1;
      }
      else if (a >= b) {
        a = a - c;
        c = c - 1;
        b = b + c*c;
      }
      else
        return;
    }
}
