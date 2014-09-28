int nondet();

void terminate(int a, int b, int c) {
    int tmp0 = a;
    a = b;
    b = tmp0;
      while (a >= c && 100 >= b) {
          int tmp0 = c;
          a = a - 1;
          c = b + 1;
          b = tmp0;
      }
          return;
}
