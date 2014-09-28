int nondet();

void Example3(int a, int b) {
    int tmp0 = a;
    a = b;
    b = tmp0;
      while (254 >= b && b >= 1) {
          if (0 >= a + 1 || a >= 1) {
            b = b + 1;
          }
          else if (a == 0) {
            b = b - 1;
          }
          else
            return;
      }
          return;
}
