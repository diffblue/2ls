int nondet();

void aa_21(int a, int b, int c) {
    while (a >= b + 1 && c == a) {
        while (1) {
          if (a >= b + 1) {
            c = c - 1;
            a = a - 1;
          }
          else if (b >= a) {
            break;
          }
          else
            return;
        }
    }
}
