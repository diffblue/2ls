int nondet();

void aa_23(int a, int b, int c) {
    while (a >= b + 1) {
        while (1) {
          if (a >= b + 1 && c >= b + 1) {
            c = c - 1;
          }
          else if (a >= b + 1 && b >= c) {
            a = a - 1;
            break;
          }
          else
            return;
        }
    }
}
