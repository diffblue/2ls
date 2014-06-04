void doit(int x)
{
  int z;
  while(z<=10)
  {
    z = z + x;
    x = 0;
  }
  assert(z>=0);
}
