#include <stdlib.h>

int *foo(int *x)
{
  return x;
}

void main()
{
  int x = 0;
  int *y;

  y = foo(&x);

  assert(y!=NULL);
}
