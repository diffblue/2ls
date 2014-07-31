#include <assert.h>

unsigned int rec2 (unsigned int x);

unsigned int rec1 (unsigned int x) {
  return rec2(x + 1);
}

unsigned int rec2 (unsigned int x) {
  return rec1(x - 1);
}

int main (void) {
  unsigned int x;

  rec1(x);

  assert(x == 0);

  return 1;
}

