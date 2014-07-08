int foo(int x)
{
  int y;
  if(y) return foo(x);
  return x;
}

void main()
{
  int x = 5;  

  x = foo(x);

  assert(x==5);
}
