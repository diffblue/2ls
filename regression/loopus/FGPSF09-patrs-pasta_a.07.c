int nondet();

void a(int a, int b, int c) {
    while (a >= b + 1 && a >= c + 1) {
      c = c + 1;
      b = b + 1;
    }
}
