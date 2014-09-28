int nondet();

void gcd(int a, int b) {
    if (0 >= a || 0 >= b) {
        return;
    }
    else if (b >= 1 && a >= 1) {
      while (a >= b + 1 || b >= a + 1) {
          if (a >= b + 1) {
            a = a - b;
          }
          else if (b >= a) {
            b = b - a;
          }
          else
            return;
      }
          return;
    }
    else
      return;
}
