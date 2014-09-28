int nondet();

void nd_loop(int a, int b) {
    a = 0;
      while (b >= a + 1 && 2 + a >= b && 9 >= b) {
        a = b;
        b = nondet();
      }
      b = nondet();
          return;
}
