#include <stdlib.h>

void main()
{
  int x[10];
  int *end = &x[9];
  int *p = x;
  for(; p!=end; p++);
  assert(p==end);
}
