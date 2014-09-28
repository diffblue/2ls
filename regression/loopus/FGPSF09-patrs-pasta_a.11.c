int nondet();

void a(int a, int b, int c) {
    while (a >= b + 1) {
        if (a >= c + 1) {
          b = b + 1;
        }
        else if (a >= c + 1) {
          c = c + 1;
        }
        else if (c >= a) {
          a = a - 1;
        }
        else
          return;
    }
}
