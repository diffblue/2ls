int nondet();

void wise(int a, int b) {
    if (0 >= a + 1 || 0 >= b + 1) {
        return;
    }
    else if (b >= 0 && a >= 0) {
      int tmp0 = a;
      a = b;
      b = tmp0;
      while (b >= a + 3 || a >= b + 3) {
          if (a >= b + 1) {
            b = b + 1;
          }
          else if (b >= a) {
            a = a + 1;
          }
          else
            return;
      }
          return;
    }
    else
      return;
}
