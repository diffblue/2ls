int nondet();

void complex(int a, int b, int c, int d, int e) {
    int tmp0 = a;
    a = b;
    b = tmp0;
      while (29 >= b) {
        c = a;
        d = b;
          while (1) {
            if (d >= c + 1) {
              if ((2 >= c && c >= 6) || c >= 6) {
                e = c + 7;
                c = e;
                d = d + 1;
              }
              else if (c >= 3 && c >= 6 && 5 >= c) {
                e = c + 7;
                d = d + 10;
                c = e;
              }
              else if ((7 >= c && 5 >= c) || (c >= 11 && 5 >= c)) {
                e = c + 2;
                c = e;
                d = d + 1;
              }
              else if (c >= 8 && 5 >= c && 10 >= c) {
                e = c + 2;
                d = d + 10;
                c = e;
              }
              else
                return;
            }
            else if (c >= d) {
              b = d + 2;
              a = c - 10;
                break;
            }
            else
              return;
          }
      }
          return;
}
