int nondet();

void aa_05(int a, int b, int c) {
    while (2*c >= 1 && a == 2*c && 1 + 2*b >= 2*c && 2*c >= 2*b) {
      c = nondet();
      a = 2*c - 1;
      b = nondet();
    }
}
