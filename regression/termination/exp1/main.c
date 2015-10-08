void main()
{
  int x;
  __CPROVER_assume(x>0);

  while(x>0)
  {
    x >>= 1;
  }
  assert(x==0);
}
