int g;

void foo() 
{ 
  g=10;
}

int bar() 
{ 
  return 20;
}

void main()
{
  g = 1;
  int x;
  foo();
  x = bar();
  assert(g==10);
  assert(x==20);
}

