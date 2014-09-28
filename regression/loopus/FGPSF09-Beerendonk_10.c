int nondet();

void aa_10(int a, int b, int c, int d, int e, int f) {
    while (1) {
      if (0 >= 2*b && a == 1 && 2*b >= 0) {
        f = nondet();
        d = nondet();
        b = nondet();
        c = nondet();
        e = nondet();
        a = 0;
      }
      else if (a == 1 + 2*b && 2*b >= 0 && 2 + 2*b >= 0) {
        f = nondet();
        d = nondet();
        b = nondet();
        c = nondet();
        e = nondet();
        a = 2*b;
      }
      else if ((3*e >= 2 && 2*c >= 0 && 2*d >= 1 && a == 1 && b >= e && 1 >= 2*f && 3*f >= 2 && 1 >= 2*e && f >= b && 1 >= 2*d && 1 >= 2*c) || (a == 2*d && 3*f >= 2*d + 1 && 2*d >= 1 && 2*d >= 2*c && 1 + 2*d >= 0 && b >= e && 1 + 2*c >= 2*d && 3*e >= 2*d + 1 && 2*d >= 2*f && f >= b && 2*d >= 2*e)) {
        d = nondet();
        e = nondet();
        a = b;
        b = nondet();
        c = nondet();
        f = nondet();
      }
      else
        return;
    }
}
