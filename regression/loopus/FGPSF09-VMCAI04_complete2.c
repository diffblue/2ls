int nondet();

void complete2(int a, int b) {
    while (b + 2*a >= 10 && 10 >= 2*a + b && a >= 0) {
      a = b;
      b = nondet();
    }
}
