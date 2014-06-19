int x;
int z;

int foo() 
{ 
  for(x=0;x<10;x++);
  return 0;
}

void main()
{
  for(z=10;z<20;z++);
  int y = foo();
  assert(x==10);
  assert(z==20);
}

