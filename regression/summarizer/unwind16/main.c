void main()
{
  int x, z;  
  __CPROVER_assume(x>=0);
  int y = 0;

  while(x>0)
  { 
    if(z)  y = y + x;
    else break;
    x -= 3;
  }

  assert(x>=-3);
}
