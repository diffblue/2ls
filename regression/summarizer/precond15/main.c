void foo1()
{
  assert(0);
}

void foo2()
{
}

void foo3(int x)
{
  assert(x==0);
}

void bar()
{
  foo1();
  foo2();

  int x;
  if(x>=0) foo3(x);
}

void main()
{
  bar();
}

