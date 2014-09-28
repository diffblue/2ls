int nondet();

void ack(int a, int b, int c) {
    while (1) {
      if (b >= 1 && a >= 1) {
        b = c;
        c = nondet();
        a = a - 1;
      }
      else if (b >= 1 && a >= 1) {
        b = b - 1;
        c = nondet();
      }
      else
        return;
    }
}
