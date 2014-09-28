int nondet();

void a(int a, int b, int c, int d, int e) {
    while (1) {
      if (e + 1 >= d && b >= a + 1 && a + b >= 2*c && 3*e >= a + b + 1 && a + b >= 2*e && 3*c >= a + b + 1 && b >= 0 && d >= c + 1 && a >= 0) {
        e = nondet();
        c = nondet();
        a = d;
        d = nondet();
      }
      else if (e >= d && b >= a + 1 && a + b >= 2*c && 3*e >= a + b + 1 && a + b >= 2*e && d >= c && 3*c >= a + b + 1 && b >= 0 && a >= 0) {
        b = d;
        d = nondet();
        c = nondet();
        e = nondet();
      }
      else
        return;
    }
}
