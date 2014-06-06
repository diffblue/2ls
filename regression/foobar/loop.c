void doit(int x)
{
  __CPROVER_assume(x>=5);
  int z = 0;
  while(z<=10)
  {
    z = z + x;
    x = 0;
  }
  assert(z>=0);
}
