int nondet();

void ax(int a, int b, int c) {
    a = 0;
      while (1) {
        b = 0;
          while (1) {
            if (c >= 2 + b) {
              b = b + 1;
            }
            else if (b + 1 >= c) {
              if (c >= 3 + a && b + 1 >= c) {
                a = a + 1;
                break;
              }
              else if (c >= 2 + b || a + 2 >= c) {
                  return;
              }
              else
                return;
            }
            else
              return;
          }
      }
}
