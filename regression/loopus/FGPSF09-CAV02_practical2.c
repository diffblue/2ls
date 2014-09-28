int nondet();

void practical2(int a, int b, int c, int d) {
  a = b;
  c = 1;
    if (a >= 101) {
      return;
    }
    else if (100 >= a) {
      while (100 >= a) {
        a = a + 11;
        c = c + 1;
      }
        while (c >= 2) {
          a = a - 10;
          c = c - 1;
            if (a >= 101 && c == 1) {
              d = a - 10;
            }
            else if (100 >= a || 2 >= c || c >= 0) {
              if (a >= 101) {
                a = a - 10;
                c = c - 1;
                a = a + 11;
                c = c + 1;
              }
              else if (100 >= a) {
                a = a + 11;
                c = c + 1;
              }
              else
                return;
            }
            else
              return;
        }
    }
    else
      return;
}
