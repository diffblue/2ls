//by Fonenantsoa Maurica

#include <assert.h>

void main()
{
  double x = 0;
  while(x + 1 > x) {
    x = x + 1;
  }
  assert(x>=1E20);
}
