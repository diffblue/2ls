int nondet();

void a(int a, int b) {
    while (1) {
      if (a >= b + 1 || (a >= b + 1 && b >= a + 1)) {
        b = b + 1;
      }
      else if ((a >= b + 1 && b >= a) || (b >= a + 1 && b >= a)) {
        a = a + 1;
      }
      else
        return;
    }
}
