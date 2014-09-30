void main()
{
  int x,y,z;  
  __CPROVER_assume(x>=0);
  __CPROVER_assume(-20<=z && z<=-1);

  do
  {
    if(y) x--;
    else x += z;
  }
  while(x>0);

  assert(x>=z);
}
