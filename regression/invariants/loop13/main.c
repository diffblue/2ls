void main()
{
  int x;  
  __CPROVER_assume(x>=0);

  do
  {
    x -= 3;
  }
  while(x>0);

  assert(x>=-3);
}
