int nondet();

void choice(int a, int b) {
    while (1) {
      if (b >= 1 && a >= 1) {
        b = a;
        a = a - 1;
      }
      else if (b >= 1 && a >= 1) {
        int tmp0 = a + 1;
        a = b - 2;
        b = tmp0;
      }
      else
        return;
    }
}
