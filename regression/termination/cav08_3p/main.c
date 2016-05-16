/* 
  Example from Cook et al, CAV 2008
*/

int nondet_int();

void f(int x, int y, int z)
{
//  __CPROVER_assume(x<=0 || x+y<=0 || x+2*y+z<=0 || x+3*y+3*z<=0 || z<0 || z<=0 && y<=0); // precondition for termination

  while (x>0) 
  {
    x = x + y;
    y = y + z;
  }
}

int main()
{
  int x = nondet_int();
  int y = nondet_int();
  int z = nondet_int();
  
  f(x,y,z);

  return 0;
}
