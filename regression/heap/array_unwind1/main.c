#include <assert.h>
#include <stdlib.h>

void main()
{
  int *a[2];
  a[0]=malloc(sizeof(int));
  for(int i=0; i<2; ++i)
  {
    a[i]=malloc(sizeof(int));
    *a[i]=i;
  }
  assert(*a[0]==0);
  assert(*a[1]==2);
}
