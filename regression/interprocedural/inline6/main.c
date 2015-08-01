#include <assert.h>

int x;

int f00 (int y) {
  return y * x++;
}

int f01 (int z) {
  return z * x++;
}

int main (void) {
  int w;

  __CPROVER_assume(0 < w);

  x = 1;

  __CPROVER_assume(w < 1024);

  int q = f00(f01(w));

  assert((q >> (x - 2)) == w);

  return 1;
}

