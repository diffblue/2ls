#include <assert.h>

void main()
{
  int z= 0;
  for(int x=0;x<1;x++)
  {
    for(int y=0;y<1;y++)
    {
      z++;
    }
  }
  assert(z==1);
}
