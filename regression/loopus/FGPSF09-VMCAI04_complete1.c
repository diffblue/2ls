int nondet();

void complete1(int a, int b, int c, int d) {
    while (a >= b + 1 && c >= 0 && d >= 1) {
      a = a - c;
      c = nondet();
      b = b + d;
      d = nondet();
    }
}
