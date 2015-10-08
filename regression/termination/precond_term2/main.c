#include <limits.h>

int foo(int y)
{
  int x=0;
  do
  {
    int x_lb = x;
    x += y;
    //assert(y>=1);
    //assert(-(x+(x+y))>0);
    //assert(!( (signed __CPROVER_bitvector[65])-1 * (signed __CPROVER_bitvector[65])x_lb <=  (signed __CPROVER_bitvector[65])-1 *  (signed __CPROVER_bitvector[65])x));
  }
  while(x<10);
//  if(0) assert(0);
  return x;
}

int main(int argc, char** argv)
{
  __CPROVER_assume(argc<=5);
  int y = argc;
  return foo(y-1);
}
