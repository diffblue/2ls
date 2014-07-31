int foo(int x) 
{ 
  int res = 0;
  if(x) res = 1;
  return res;
}
int bar(int x) 
{   
  int res = 2;
  if(x) res = 1;
  return res; 
}

void main()
{
  int x;
  int z = bar(x);
  int w = foo(x);

  assert(1<=z && z<=2);
  assert(0<=w && w<=z);
}

