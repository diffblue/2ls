int foo() 
{ 
  return 1;
}
int bar() 
{   
  return 2; 
}

void main()
{
  int x = bar() + foo();
  assert(x==3);
}

