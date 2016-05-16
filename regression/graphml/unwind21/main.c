#include "../svcomp.h"

int foo(int x)
{
  return x+1;
}

void main()
{
  int x=0;
  while(x<10)
  {
    x = foo(x);
  }
  __VERIFIER_assert(x==11);
}
