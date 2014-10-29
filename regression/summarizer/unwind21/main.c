int foo(int x)
{
  return x+1;
}

void main()
{
  int x=0;
  while(x<10)
  {
    x = foo(x);
  }
  assert(x==11);
}
