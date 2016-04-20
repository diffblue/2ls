#include <limits.h>

void main()
{
  int x;// = 1;  
  int y;// = 1;  
  int u;// = 0;

  assert(verify(x, y, u) != 0);

}



int verify(int x, int y, int u) {

  // check induction
  if(x > 0 && u < INT_MAX)
  {

    int x0 = x;
    int y0 = y;
    int u0 = u;

    // body
    if(y<10) x++;
    else x--;
    if(y==INT_MAX) u++;
    y++;

    // check ranking function
    if(-(long)u0 <= -(long)u && (-(long)u0 != -(long)u || (long)u0-(long)y0 <= (long)u-(long)y) /*&& (-u0 != -u || u0 != u || -y0 <= -y)*/)
    //if((long)x0 <= (long)x && ((long)x0 != (long)x || -(long)y0-(long)x0-(long)u0 <= -(long)y-(long)x-(long)u) /*&& (-u0 != -u || u0 != u || -y0 <= -y)*/)
    //if(-u0 <= -u && (-u0 != -u || -y0 <= -y))
    //if(-(long)u0+(long)x0 <= -(long)u+(long)x && (-(long)u0+(long)x0 != -(long)u+(long)x || ( -(long)u0-(long)x0 <= -(long)u-(long)x && (-(long)u0-(long)x0 != -(long)u-(long)x || (long)u0+(long)x0 <= (long)u+(long)x))))
    //if((long)x0 <= (long)x && ((long)x0 != (long)x || -(long)u0-(long)x0 <= -(long)u-(long)x))
    // if(-(long)u0+(long)x0 <= -(long)u+(long)x && (-(long)u0+(long)x0 != -(long)u+(long)x || 
    //						    (-(long)u0-(long)x0 <= -(long)u-(long)x && (-(long)u0-(long)x0 != -(long)u-(long)x || 
    //												(long)u0+(long)x0 <= (long)u+(long)x))))
      return 0;
  }

  return 1;
}
