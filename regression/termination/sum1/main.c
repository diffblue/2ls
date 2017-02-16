#include <limits.h>

int max(int x, int y) 
{ 
  if(x>y) return x;
  return y; 
}

int inv(int x) 
{   
  __CPROVER_assume(x>INT_MIN); //would not be needed if we did not extend the bitvector sizes
  return -x; 
}

void main()
{
  int x; 
  __CPROVER_assume(2<=x && x<=3);

  int y=inv(x);
  int z=max(y,0);

  assert(y<=-2);
  assert(y==-x);
  assert(z>=0);
  assert(z>=y);
}
