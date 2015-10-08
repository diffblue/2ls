#include <limits.h>

void main()
{
  int x = 1;  
  int y = 1;  
  int u = 0;

  while(x>0 && u < INT_MAX) //-u, -y, x
  {
    if(y<10) x++;
    else x--;
    if(y==INT_MAX) u++;
    y++;
  }
}
