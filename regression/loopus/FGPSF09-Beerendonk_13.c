int nondet();

void aa_13(int a, int b) {
    while (1) {
      if (b >= a && a >= 1) {
        a = a - 1;
      }
      else if (a >= b + 1 && a >= 1) {
        a = b;
      }
      else
        return;
    }
}
