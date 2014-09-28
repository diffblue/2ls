int nondet();

void ex13(int a, int b, int c, int d, int e, int f) {
    int tmp0 = a;
    a = b;
    b = c;
    c = d;
    d = tmp0;
      while (a >= d) {
        e = b;
          while (1) {
            if (c >= e) {
              f = d - e;
                while (1) {
                  if (d + e >= f) {
                    f = f + 1;
                  }
                  else if (f >= d + e + 1) {
                    e = e + 1;
                      break;
                  }
                  else
                    return;
                }
            }
            else if (e >= c + 1) {
              d = d + 1;
                break;
            }
            else
              return;
          }
      }
          return;
}
