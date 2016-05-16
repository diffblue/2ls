int foo(int x) 
{ 
  if(x) return 9;
  return 10;
}

void main()
{
  int x;
  x = foo(x);
  assert(9<=x && x<=10);
}


