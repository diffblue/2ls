int nondet();

void Example5(int a, int b, int c) {
    if (b >= a + 1 && a >= 1) {
      int tmp0 = a;
      a = c;
      c = tmp0;
        while (c >= 1 && b >= c + 1) {
            if (a >= 1) {
              c = c + 1;
            }
            else if (0 >= a) {
              c = c - 1;
            }
            else
              return;
        }
            return;
    }
    else
        return;
}
