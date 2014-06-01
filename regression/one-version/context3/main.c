#include <stdlib.h>

void main()
{
  int i;
  
  if(i==1)
  {
    // should pass, due to postcondition of exit()
    exit(0);
    assert(0);
  }
  else if(i==2)
  {
    // should pass, due to postcondition of _Exit()
    _Exit(0);
    assert(0);
  }
  else if(i==3)
  {
    // should pass, due to postcondition of abort()
    abort();
    assert(0);
  }
} 

