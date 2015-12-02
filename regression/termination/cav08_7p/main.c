/* 
  Example from Cook et al, CAV 2008
*/

unsigned nondet_int();

void f(int x, int y)
{
//  __CPROVER_assume(x==y || x>0 && y>0); // precondition for termination

  while (x!=y) 
  { 
    if (x>y) 
    {
      x=x-y;
    } 
    else
    {
      y=y-x;
    }
  }
}

int main()
{
  int x = nondet_int();
  int y = nondet_int();
  
  f(x,y);

  return 0;
}
