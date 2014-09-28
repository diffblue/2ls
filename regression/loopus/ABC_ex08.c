int nondet();

void ex08(int a, int b, int c) {
    int tmp0 = a;
    a = b;
    b = tmp0;
      while (b >= 1) {
        c = a;
          while (1) {
            if (c >= 1) {
              c = c - 1;
            }
            else if (0 >= c) {
              b = b - 1;
                break;
            }
            else
              return;
          }
      }
          return;
}
