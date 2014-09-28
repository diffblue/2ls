int nondet();

void sipma91(int a, int b, int c, int d) {
    if (a >= 101) {
        return;
    }
    else if (100 >= a) {
      b = a;
      a = 1;
      while (100 >= b) {
          a = a + 1;
          b = b + 11;
      }
        while (a >= 2) {
            if (110 >= b || 1 >= a || a >= 3) {
              d = a - 1;
              c = b - 10;
              if (c >= 101) {
                b = c + 1;
                a = d;
              }
              else if (c >= 101 && 100 >= c) {
                a = d;
                b = c + 11;
              }
              else if (c >= 101 && 100 >= c) {
                a = d + 1;
                b = c + 1;
              }
              else if (100 >= c) {
                a = d + 1;
                b = c + 11;
              }
              else
                return;
            }
            else if (a == 2 && b >= 111) {
              b = b - 10;
              a = a - 1;
            }
            else
              return;
        }
            return;
    }
    else
      return;
}
