int nondet();

void aa_19(int a, int b, int c) {
    while (1) {
      if (a >= b + 1 || (a >= b + 1 && c >= b + 1)) {
        a = a - 1;
      }
      else if ((a >= b + 1 && c >= b + 1 && b >= a) || (c >= b + 1 && b >= a)) {
        c = c - 1;
      }
      else if ((a >= b + 1 && b >= c && b >= a) || (c >= b + 1 && b >= c && b >= a)) {
      }
      else
        return;
    }
}
