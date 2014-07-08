#include <stdlib.h>

void foo(int **x)
{
  x = NULL;
}

void main()
{
  int x = 0;
  int *p = &x;
  int *y = p;
  for(int i=0;i<10;i++)  foo(y);
  assert(y==NULL);
}
