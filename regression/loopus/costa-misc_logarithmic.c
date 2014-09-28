int nondet();

void logarithmic(int a, int b) {
  if (a >= 1 || a >= 2 || a >= 4) {
    b = nondet();
      while (a >= 2 && 3*b >= 2 && 1 >= 2*b) {
        a = a*b;
        b = nondet();
      }
  }
  else
      return;
}
