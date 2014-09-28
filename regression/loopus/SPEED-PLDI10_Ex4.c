int nondet();

void Ex4(int a, int b, int c, int d, int e) {
    b = a;
    a = 1;
      while (a == 1) {
        d = b;
        c = 0;
        e = nondet();
          while (1) {
            if (0 >= d) {
              b = d;
              e = nondet();
              a = c;
              break;
            }
            else if (d >= 1) {
              e = nondet();
              if (0 >= e + 1 || e >= 1) {
                e = nondet();
                d = d - 1;
                c = 1;
              }
              else if (1) {
                b = d;
                a = c;
                break;
              }
              else
                return;
            }
            else
              return;
          }
      }
      e = nondet();
          return;
}
