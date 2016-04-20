/* 
  Example from Cook et al, CAV 2008
*/

unsigned nondet_int();

void f(int y, int n)
{
  __CPROVER_assume(n>200 && y<9); //additional assumption given
  __CPROVER_assume(y>0); // precondition for termination
  int x = 0;
  while (1) 
  {
    if (x<n) 
    {   
      x = x + y;
      if (x >= 200) break;
    }
  }
}

int main()
{
  int y = nondet_int();
  int n = nondet_int();
  
  f(y,n);

  return 0;
}
