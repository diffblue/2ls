int foo(int x, int y) 
{ 
  int res = y;
  if(x) res = 0;
  return res;
}
int bar(int x) 
{   
  if(x) return 1;
  return return 2
}

void main()
{
  int x;
  int y = 0;
  int z = bar(x);
  int w = foo(x,y);

  assert(1<=z && z<=2);
  assert(w<=z);
}

