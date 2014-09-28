int nondet();

void aa_07(int a, int b) {
    while (a == 1 + 2*b && 2*b >= 0) {
      a = -2 + 2*b;
      b = nondet();
    }
}
