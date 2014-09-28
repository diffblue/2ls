int nondet();

void aa_22(int a, int b) {
    while (a >= 1) {
        while (1) {
          if (b >= 1 && a >= 1) {
            b = b - 1;
          }
          else if (0 >= b && a >= 1) {
            a = a - 1;
            break;
          }
          else
            return;
        }
    }
}
