
int x = 1;

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
  int y = do1(x);
  assert(-1<=y && y<=1);
  x = -x;
  int z = do2(x);
  assert(z==-1);
}

