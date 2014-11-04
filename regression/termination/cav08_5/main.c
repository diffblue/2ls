/* 
  Example from Cook et al, CAV 2008
*/

unsigned nondet_int();

void f(int x)
{
  __CPROVER_assume(x>5 || x<0);
  
  while (x>=0) 
  {
    x = -2*x + 10;
  }
}

int main()
{
  int x = nondet_int();
  
  f(x);

  return 0;
}
