int nondet();

void terminate(int a, int b, int c) {
    while (100 >= a && b >= c) {
      int tmp0 = a + 1;
      a = c;
      c = tmp0;
      b = b - 1;
    }
}
