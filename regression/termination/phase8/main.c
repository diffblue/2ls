#include <limits.h>

void main()
{
  int x = 1;  
  int y = 1;  
  int u = 0;
  int w = 0;
 
  while(x>0 && w<INT_MAX) //three lexicographic components -w, -u, -y
  {
    if(y<10) x++;
    else x--;
    if(y==INT_MAX) {
      if (u==INT_MAX) {
	w++;
      }
      u++;
    }
    y++;
    if(y<100) y++;
  }
  assert(x==0);
}
