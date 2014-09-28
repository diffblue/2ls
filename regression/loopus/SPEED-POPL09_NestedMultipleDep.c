int nondet();

void NestedMultipleDep(int a, int b, int c, int d, int e) {
    a = 0;
      while (b >= a + 1) {
          c = a + 1;
          d = 0;
            while (1) {
              if (e >= d + 1) {
                d = d + 1;
              }
              else if (d >= e) {
                a = c;
                break;
              }
              else
                return;
            }
      }
          return;
}
