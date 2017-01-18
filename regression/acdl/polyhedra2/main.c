int main()
{
  int x,y,z;
  __CPROVER_assume(x==y);
  z=x-y;
  assert(z==0);
}
