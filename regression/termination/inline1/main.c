#include <assert.h>

unsigned int square (unsigned int x) {
  return x * x;
}

unsigned int nondet_ui();

int main (void) {
  unsigned int x = nontdet_ui();
  unsigned int y = square(x);

  assert((y & 0x2) == 0x0);

  return 1;
}

