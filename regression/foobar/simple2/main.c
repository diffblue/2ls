int foo(int x) 
{ 
  return x;
}

void main()
{
  int x = 10;
  x = foo(x);
  assert(x==10);
}

