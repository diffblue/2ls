/* 
  Example from Cook et al, CAV 2008
*/

int nondet_int();

void f(int l_var)
{
  __CPROVER_assume(l_var> 0 || l_var<0 || l_var>=1073741824); // precondition for termination
  int  i=0;
  if (l_var >= 0) 
  {
    while (l_var < 1073741824) 
    {
      i++;
      l_var = l_var << 1;
    }
  }
}

int main()
{
  int l_var = nondet_int();
  
  f(l_var);

  return 0;
}
