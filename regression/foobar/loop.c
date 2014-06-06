void doit(int x)
{
  __CPROVER_assume(x>=5);
  int z = 0;
  while(z<=10)
  {
    z = z + x;
  }
  assert(z>=0);
}
