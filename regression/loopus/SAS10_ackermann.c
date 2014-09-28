int nondet();

void ackermann(int a, int b, int c, int d, int e) {
  d = a;
  e = nondet();
  c = b;
  while (c >= 0 && d >= 1 && d >= 0 && b >= 0 && a >= 0 && a >= d) {
    e = nondet();
      c = c - 1;
      e = nondet();
        d = d - 1;
        c = e;
        e = nondet();
          if (0 >= c + 1 && a >= d + 1 && b >= 0 && d >= 0) {
            e = nondet();
          }
          else {
            e = nondet();
            break;
          }
      d = d - 1;
      c = 1;
      e = nondet();
  }
  e = nondet();
}
