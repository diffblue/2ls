
int sign(int x) 
{ 
  if(x>0) return 1;
  else if (x==0) return 0;
  return -1;
}

void main()
{
  int x;
  int y = sign(x);
  assert(y==0);
}

