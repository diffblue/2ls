#include <stdlib.h>

int *foo()
{
  return NULL;
}

void main()
{
  int x = 0;
  int *p = &x;
  int *y = p;
  for(int i=0;i<10;i++)  y = foo();
  assert(y==NULL);
}
