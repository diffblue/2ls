void bar()
{
  while(1);
}

int foo(int x)
{
  return x;
}

void main()
{
  int x = 1;
  if(x) x = foo(x);
  else bar(); //unreachable
}
