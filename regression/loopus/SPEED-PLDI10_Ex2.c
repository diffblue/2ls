int nondet();

void Ex2(int a, int b, int c, int d, int e) {
      while (a >= 1 && b >= 1) {
        e = nondet();
          d = b - 1;
          c = a - 1;
            while (1) {
              if (0 >= e + 1 || e >= 1) {
                e = nondet();
                d = d - 1;
                c = c + 1;
              }
              else if (1) {
                b = d;
                a = c;
                break;
              }
              else
                return;
            }
      }
      e = nondet();
          return;
}
