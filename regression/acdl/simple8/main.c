#include "assert.h"

struct int4_s {
 int a, b, c, d;
};

int A[400];

int main()
{
  int * x;
  int * y;
  struct int4_s* x4;
  struct int4_s* y4;


  x = A;

  y = x;

  y4 = (struct int4_s*) x;

  x4 = (struct int4_s*) x;


  assert(x == A);
  assert(x == (int*) x4);
  assert(x == y);
  assert(y4 == x4);
  assert(y == (int*) x4);

  return 0;
}
