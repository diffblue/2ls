
int foo(int x) 
{   
  int res;
  if(x) return 0;
  else return 1;
}

int bar(int x) 
{   
  int res;
  if(x) res = 0;
  else res = 1;
  return res;
}

void main()
{
  int x;
  int y = foo(x);
  assert(0<=y && y<=1);
  y = bar(x);
  assert(0<=y && y<=1);
}

