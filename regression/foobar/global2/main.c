int g;

int foo() 
{ 
  g=10;
  return 0;
}

int bar() 
{ 
  return 20;
}

void main()
{
  g = 1;
  int x;
  x = foo();
  x = bar();
  assert(g==10);
  assert(x==20);
}

