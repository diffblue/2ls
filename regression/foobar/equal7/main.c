int foo(int x) 
{ 
  __CPROVER_assume(x==0);
  return -x;
}

void main()
{
  int x = 0;
  x = foo(x);
  x = foo(x);
  assert(x==0);
}
