int foo(int x, int y) 
{ 
  return x;
}

void main()
{
  int x = 10;
  x = foo(x,x);
  assert(x==10);
}
