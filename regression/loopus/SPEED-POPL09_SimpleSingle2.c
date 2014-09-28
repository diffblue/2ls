int nondet();

void SimpleSingle2(int a, int b, int c, int d, int e) {
    b = 0;
    a = 0;
      while (0 >= e + 1 || e >= 1) {
        e = nondet();
          if (c >= b + 1) {
            e = nondet();
            b = b + 1;
            a = a + 1;
          }
          else if (b >= c) {
            e = nondet();
            if (d >= a + 1) {
              e = nondet();
              b = b + 1;
              a = a + 1;
            }
            else if (a >= d) {
              e = nondet();
                return;
            }
            else
              return;
          }
          else
            return;
      }
          return;
}
