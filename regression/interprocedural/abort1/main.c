int foo(int x)
{
  if(x>0) while(1);
  return x;
}

void main()
{
  int x;
  x = foo(x);  
  assert(x<=0);
}
