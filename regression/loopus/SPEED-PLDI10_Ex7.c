int nondet();

void Ex7(int a, int b, int c) {
    if (b >= a + 1 && a >= 1) {
      c = a + 1;
        while (a >= c + 1 || c >= a + 1) {
            if (c >= b + 1) {
              c = 0;
            }
            else if (b >= c) {
              c = c + 1;
            }
            else
              return;
        }
            return;
    }
    else
        return;
}
