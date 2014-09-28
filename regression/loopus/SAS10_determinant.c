int nondet();

void determinant(int a, int b, int c, int d, int e, int f, int g, int h) {
  e = f;
  c = d;
  b = a;
  g = h;
  c = 1;
  while (a >= c + 1 && c >= 1 && a >= c && b == a && a >= 1) {
    g = 1 + c;
      while (a >= c + 1 && c >= 1 && a + 1 >= g && a >= g && g >= c + 1 && b == a) {
        e = b;
          while (e >= c && e >= c + 1 && c >= 1 && a >= g && g >= c + 1 && a >= e && b == a) {
            e = e - 1;
          }
          g = 1 + g;
      }
      c = 1 + c;
  }
}
