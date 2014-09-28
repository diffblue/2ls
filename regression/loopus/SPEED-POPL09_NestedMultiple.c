int nondet();

void NestedMultiple(int a, int b, int c, int d, int e, int f) {
    int tmp1 = c;
    int tmp0 = a;
    c = d;
    d = tmp1;
    a = b;
    b = tmp0;
      while (a >= b + 1) {
        f = nondet();
        e = d;
          while (1) {
            if (e >= c) {
              f = nondet();
              d = e;
              b = b + 1;
                break;
            }
            else if (c >= e + 1) {
              f = nondet();
              if (0 >= f + 1 || f >= 1) {
                f = nondet();
                e = e + 1;
              }
              else if (1) {
                d = e;
                b = b + 1;
                  break;
              }
              else
                return;
            }
            else
              return;
          }
      }
      f = nondet();
          return;
}
