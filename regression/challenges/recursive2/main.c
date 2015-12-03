int foo(int x)
{
  if(x<10) return foo(x+1);
  return x;
}

void main()
{
  int x = 0;  

  x = foo(x);

  assert(x>=10);
}
