int nondet();

void complete4(int a, int b, int c) {
    while (1) {
      if (a >= 0) {
        b = c;
        c = nondet();
        a = a - 1;
      }
      else if (b >= 0) {
        b = b - 1;
        c = nondet();
      }
      else
        return;
    }
}
