extern int nondet();

void main()
{
  int x;  
  __CPROVER_assume(x>=0);
  int y = 0;

  do
  {
    int z = nondet();
    if(z)  y = y + x;
    x -= 3;
  }
  while(x>0);

  assert(x>=-3);
}
