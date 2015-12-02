#include "../svcomp.h"

void main()
{
  int x;
  for(x=0;x<10;x++)
  {
    if(x==3) break;
  }
  __VERIFIER_assert(x==10);
}
