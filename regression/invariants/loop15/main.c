void main()
{
  int x,y,z;  
  __CPROVER_assume(x>=0);
  __CPROVER_assume(x==y);
  __CPROVER_assume(-1<=z && z<=-1);

  do
  {
    x--;
    y += z;
  }
  while(x>0);

  assert(x==y);
}
