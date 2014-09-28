int nondet();

void abstractions(int a, int b, int c) {
    while (1) {
      if (b >= 1 && a >= 1) {
        a = a - 1;
        b = c;
        c = nondet();
      }
      else if (b >= 1 && a >= 1) {
        c = nondet();
        b = b - 1;
      }
      else
        return;
    }
}
