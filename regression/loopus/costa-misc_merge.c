int nondet();

void merge(int a, int b) {
    while (1) {
      if (b >= 1 && a >= 1) {
        a = a - 1;
      }
      else if (b >= 1 && a >= 1) {
        b = b - 1;
      }
      else
        return;
    }
}
