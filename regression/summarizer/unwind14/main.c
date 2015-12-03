void main()
{
  int x, z;  
  __CPROVER_assume(x>=0);
  int y = 0;

  do
  { 
    if(z)  y = y + x;
    else break;
    x -= 3;
  }
  while(x>0);

  assert(x>=-3);
}
