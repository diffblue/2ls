/* 
  Example from Cook et al, CAV 2008
*/

unsigned nondet_int();

void f(int x, int y, int N)
{
//  __CPROVER_assume(x>N || x+y>=0); // precondition for termination
  
  while (x<=N) 
  {
    int c;
    if(c) 
    {
      x = 2*x + y;
      y = y + 1;
    }
    else
    {
      x++;
    }
  }
}

int main()
{
  int x = nondet_int();
  int y = nondet_int();
  int N = nondet_int();
  
  f(x,y,N);

  return 0;
}
