int nondet();

void Ex6(int a, int b, int c) {
      while (c >= b + 1) {
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
