#include <assert.h>

unsigned int square1 (unsigned int x) {
  return x * x;
}

unsigned int square2 (unsigned int x) {
  x = x;
  return x * x;
}

unsigned int nondet_ui();

int main (void) {
  unsigned int x = nontdet_ui();
  unsigned int y = square1(x);
  unsigned int z = square2(x);

  assert((y & 0x2) == 0x0);
  assert((z & 0x2) == 0x0); //expected to fail

  return 1;
}

