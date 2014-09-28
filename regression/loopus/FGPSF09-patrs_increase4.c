int nondet();

void increase4(int a, int b) {
    while (a >= b + 1) {
      b = b + 2;
      a = a + 1;
    }
}
