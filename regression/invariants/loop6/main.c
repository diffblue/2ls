#include <assert.h>

void main()
{
  int x = 0;
  unsigned y = 0;
  
  while(x<10 && y<20)
  {
    ++x;
    ++y;
  }
  
  int z=x+y;
  assert(z<=20);
}
