int nondet();

void aa_06(int a, int b) {
    while (a == 1 + 2*b && 2*b >= 0) {
      b = nondet();
      a = 2*b;
    }
}
