int nondet();

void mspe(int a, int b, int c, int d, int e, int f, int g, int h) {
  if (b + a + 2 >= 2*c && f == a && b >= a + 1 && e + 1 == c && d >= 0 && 2*c >= b + a && a >= 0) {
    h = nondet();
    g = nondet();
      while (1) {
        if (b + 1 >= g && f + 1 >= g && c + 1 >= h && g >= 1 + f && d >= 0 && h >= 1 + c && a >= e + 1 && b >= 1) {
          f = g;
          g = nondet();
          c = h;
          h = nondet();
        }
        else if (c >= b + 1 && a + 1 >= h && e + 1 >= h && b >= f && f + 1 >= g && h >= 1 + a && g >= 1 + f && d >= 0 && b >= 1) {
          a = h;
          h = nondet();
          f = g;
          g = nondet();
        }
        else if (b + 1 >= h && e >= a && b >= f && c + 1 >= h && f + 1 >= g && g >= 1 + f && d >= 0 && h >= 1 + c && b >= 1) {
          c = h;
          h = nondet();
          f = g;
          g = nondet();
        }
        else if (a + 1 >= h && e + 1 >= h && b >= c && b >= f && f + 1 >= g && g >= 1 + f && h >= 1 + a && d >= 0 && b >= 1) {
          a = h;
          h = nondet();
          f = g;
          g = nondet();
        }
        else
          return;
      }
  }
  else
      return;
}
