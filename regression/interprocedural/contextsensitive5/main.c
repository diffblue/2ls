#include <stdlib.h>

void foo(int* x) 
{ 
  assert(x!=NULL);
  *x = 0;
}

void main()
{
  int x;
  int *y = &x;
  foo(y);
}

