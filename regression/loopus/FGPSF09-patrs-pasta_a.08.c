int nondet();

void a(int a, int b) {
    while (a >= b + 1) {
      a = a + 1;
      b = b + 2;
    }
}
