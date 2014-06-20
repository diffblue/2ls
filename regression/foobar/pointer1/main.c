int foo(int *x) 
{ 
  *x = 10;
  return 0;
}

void main()
{
  int x;
  int y = foo(&x);
  assert(x==10);
}

