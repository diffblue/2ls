#include <assert.h>
#include <stdint.h>

int collatz (uint64_t x) {
  if (x == 1) {
    return 1;
  } else {
    if ((x & 1) == 0) {
      return collatz(x >> 1);
    } else {
      return collatz(3 * x + 1);
    }
  }
}

uint64_t nondet_uint64_t (void);

int main (void) {
  uint64_t x = nondet_uint64_t();
  int z = collatz(x);

  assert(z);

  return 1;
}

