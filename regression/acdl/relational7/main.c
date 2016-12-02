#include <stdlib.h>
#include <assert.h>
int main()
{
  signed x,y;
  int z;
  
  __CPROVER_assume(x==y || x==-y);
  z = (x<0?-x:x) - (y<0?-y:y);
  
  assert(z==0);
}

