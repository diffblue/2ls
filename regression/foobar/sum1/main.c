int max(int x, int y) 
{ 
  if(x>y) return x;
  else return y; 
}

int inv(int x) 
{   
  int res = -x; 
  return res;
}

void main()
{
  int x; 
  __CPROVER_assume(2<=x && x<=3);

  int y=inv(x);
  int z=max(y,0);

  assert(z<=x);
}
