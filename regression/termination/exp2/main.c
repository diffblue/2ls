void main()
{
  int x, y;
  __CPROVER_assume(x>0);
  __CPROVER_assume(y>1);

  while(x>0)
  {
    x /= y;
  }
  assert(x==0);
}
