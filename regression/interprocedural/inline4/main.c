#include <assert.h>

int f00 (void) {
  static int i = 0;

  return ++i;
}

int f01 (int x, int y) {
  return 3*x + y;
}

int main (void) {
  int z = f01(f00(),f00());

  assert((z == 5) || (z == 7));

  return 1;
}

