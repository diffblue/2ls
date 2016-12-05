//#include <stdlib.h>
#include <assert.h>
int abs(int x) {
  return (x < 0 ? -x:x);
}

int main()
{
  signed x,y;
  int z,d,g;
  
  __CPROVER_assume(x==y || x==-y);
  z = abs(x) - abs(y);
  
  //z = (x<0?-x:x) - (y<0?-y:y);
  /*if(x<0)
    d=-x;
  else 
    d=x;  
  if(y<0)
    g=-y;
  else 
    g=y;
  z = d-g;    
  */
  assert(z==0);
}

