#include <stdlib.h>

void main()
{
  int x = 0;
  int *p = &x;
  int *y = p;
  for(int i=0;i<10;i++)  y = p;
  assert(p!=NULL);
  assert(y!=NULL);
  *y = *p;
}
