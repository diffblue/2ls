#include "../svcomp.h"

void main() {                                                                     int x;
  if(x!=4) return;
  while(x>0)
  {
    int y;
    if(-3>y || y>-1) return;
    x += y;
  }        
  __VERIFIER_assert(x==0 || x==-2);                           
} 
