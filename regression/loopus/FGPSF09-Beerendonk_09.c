int nondet();

void aa_09(int a, int b, int c) {
    while (a >= b + 1 && c >= b + 1) {
      a = a - 1;
      c = c - 1;
    }
}
