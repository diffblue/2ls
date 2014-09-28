int nondet();

void aa_20(int a, int b) {
    while (b == a && a >= 1) {
        while (1) {
          if (a >= 1) {
            b = b - 1;
            a = a - 1;
          }
          else if (0 >= a) {
            break;
          }
          else
            return;
        }
    }
}
