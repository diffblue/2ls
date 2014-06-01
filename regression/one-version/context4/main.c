#include <stdlib.h>

void f(int i, int j)
{
  if(i!=j)
    exit(0);
}

void main()
{
  int i, j;
  
  f(i, j);
  
  // should pass, due to postcondition of f
  assert(i==j);
} 

