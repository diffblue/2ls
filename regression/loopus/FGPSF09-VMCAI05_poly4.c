int nondet();

void poly4(int a, int b, int c, int d, int e) {
    while (1) {
      if (a >= b + 1 && c >= d + 1) {
        e = e + 1;
        b = b + 1;
      }
      else if ((a >= b + 1 && c >= d + 1) || (c >= d + 1 && b >= a)) {
        d = d + 1;
        e = e + 1;
      }
      else if (a >= b + 1 && d >= c) {
        b = b + 1;
        e = e + 1;
      }
      else
        return;
    }
}
