int nondet();

void sect1_quad(int a, int b) {
    while (a >= 1) {
      b = b + a;
      a = a - 1;
    }
      while (b >= 1) {
        b = b - 1;
      }
}
