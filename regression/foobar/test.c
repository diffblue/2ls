int foo(int x, int y) 
{ 
  return x+y; 
}
int bar(int x) 
{   
  int res = -x; 
  return res;
}

void doit(int x, int y)
{
  int z=bar(x);
  while(z<=10)
  {
    z = foo(bar(x),y);
    z++;
  }
  assert(z>=0);
}
