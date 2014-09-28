int nondet();

void random1d(int a, int b, int c) {
    if (a >= 1) {
      b = 1;
      c = nondet();
      while (a >= b) {
        c = nondet();
          if (0 >= c + 1 || c >= 1) {
            c = nondet();
            b = b + 1;
          }
          else if (1) {
            b = b + 1;
          }
          else
            return;
      }
      c = nondet();
          return;
    }
    else if (0 >= a) {
      c = nondet();
        return;
    }
    else
      return;
}
