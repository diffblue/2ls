int nondet();

void loops(int a, int b, int c) {
    if (a >= 0) {
      c = nondet();
      while (a >= 0) {
        c = nondet();
          if (a >= 2) {
            b = 1;
            c = nondet();
            while (1) {
              if (a >= b + 1) {
                c = nondet();
                b = 2*b;
              }
              else if (b >= a) {
                c = nondet();
                a = a - 1;
                  break;
              }
              else
                return;
            }
          }
          else if (1 >= a) {
            b = c;
            c = nondet();
            a = a - 1;
              break;
          }
          else
            return;
      }
      c = nondet();
          return;
    }
    else if (0 >= a + 1) {
      c = nondet();
        return;
    }
    else
      return;
}
