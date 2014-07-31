int x;
int z;

void foo() 
{ 
  for(x=0;x<10;x++);
}

void main()
{
  for(z=10;z<20;z++);
  foo();
  assert(x==10);
  assert(z==20);
}

