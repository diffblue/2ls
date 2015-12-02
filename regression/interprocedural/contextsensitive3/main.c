
int sign(int x) 
{ 
  if(x>0) return 1;
  else if (x==0) return 0;
  return -1;
}

int do1(int x)
{
  return sign(x);
}

int do2(int x)
{
  return sign(x);
}

void main()
{
  int x = 1;
  int y = do2(x);
  assert(y==1);
  x = -x;
  int z = do1(x);
  assert(-1<=z && z<=1);
}

