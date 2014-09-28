int nondet();

void aa_18(int a, int b) {
    while (1) {
      if (a >= 1 || (a >= 1 && b >= 1)) {
        a = a - 1;
      }
      else if ((0 >= a && b >= 1 && a >= 1) || (0 >= a && b >= 1)) {
        b = b - 1;
      }
      else if ((0 >= b && 0 >= a && a >= 1) || (0 >= b && 0 >= a && b >= 1)) {
      }
      else
        return;
    }
}
