
int sign(int x) 
{ 
  if(x>0) return 1;
  else if (x==0) return 0;
  return -1;
}

void main()
{
  int x = 1;
  int y = sign(x);
  x = -x;
  int z = sign(x);
  assert(-1<=y && y<=1 && -1<=z && z<=1);
}

