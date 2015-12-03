#include <limits.h>

int g;

int foo(int y) 
{ 
  __CPROVER_assume(g<INT_MAX);
  if(y) g++;
  return 0;
}

void main()
{
  g = 1;
  int x;
  int z = foo(x);
  g++;
  assert(g>=1);
  assert(z==0);
}

