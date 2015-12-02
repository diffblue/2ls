#include "../svcomp.h"

void main()
{
  int x;
  if(x!=0) return;
  ++x;
  __VERIFIER_assert(x!=1);
}
