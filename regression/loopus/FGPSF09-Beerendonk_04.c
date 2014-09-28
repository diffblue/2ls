int nondet();

void aa_04(int a, int b) {
    while (a >= b + 1) {
      int tmp0 = a;
      a = b;
      b = tmp0;
    }
}
