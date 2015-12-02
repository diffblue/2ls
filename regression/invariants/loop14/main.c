void main()
{
  int x,y,z;  
  __CPROVER_assume(x>=0);
  __CPROVER_assume(-20<=z && z<=-1);

  while(x>0)
  {
    if(y) x--;
    else x += z;
    assert(z>=-20);
    assert(x>=-19);
    assert(x>=z);
  }

  assert(z>=-20);
  assert(x>=-20);
  assert(x>=z); //can only be verified if relation between x and z known
}
