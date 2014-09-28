int nondet();

void aa_24(int a, int b) {
    while (1) {
      if (a >= b + 1 && b >= 1 && a >= 1) {
        while (1) {
          if (a >= 1) {
            a = a - 1;
          }
          else if (0 >= a) {
            break;
          }
          else
            return;
        }
      }
      else if (b >= a && b >= 1 && a >= 1) {
        while (1) {
          if (b >= 1) {
            b = b - 1;
          }
          else if (0 >= b) {
            break;
          }
          else
            return;
        }
      }
      else
        return;
    }
}
