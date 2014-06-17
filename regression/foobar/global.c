int g;

int foo(int y) 
{ 
  if(y) g++;
  return 0;
}

void doit(int x)
{
  g = 1;
  int z = foo(x);
  g++;
  assert(g>=1);
}
