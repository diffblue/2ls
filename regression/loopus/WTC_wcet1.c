int nondet();

void wcet1(int a, int b, int c, int d, int e) {
    if (a >= 1) {
      c = a;
      e = nondet();
      b = 0;
      while (1) {
        if (0 >= e + 1 || e >= 1) {
          e = nondet();
          if (b + 1 >= a) {
            d = 0;
            e = nondet();
            if (c >= 2) {
              e = nondet();
              c = c - 1;
              b = d;
            }
            else if (1 >= c) {
              e = nondet();
                return;
            }
            else
              return;
          }
          else if (a >= b + 2) {
            e = nondet();
            d = b + 1;
            if (c >= 2) {
              e = nondet();
              c = c - 1;
              b = d;
            }
            else if (1 >= c) {
              e = nondet();
                return;
            }
            else
              return;
          }
          else
            return;
        }
        else if (1) {
          if (1 >= b) {
            e = nondet();
            d = 0;
              if (c >= 2) {
                e = nondet();
                c = c - 1;
                b = d;
              }
              else if (1 >= c) {
                e = nondet();
                  return;
              }
              else
                return;
          }
          else if (b >= 2) {
            e = nondet();
            d = b - 1;
            if (c >= 2) {
              e = nondet();
              c = c - 1;
              b = d;
            }
            else if (1 >= c) {
              e = nondet();
                return;
            }
            else
              return;
          }
          else
            return;
        }
        else
          return;
      }
    }
    else if (0 >= a) {
      e = nondet();
        return;
    }
    else
      return;
}
