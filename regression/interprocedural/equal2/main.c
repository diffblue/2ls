unsigned foo(unsigned x, unsigned y) 
{ 
  __CPROVER_assume(x<10*y && y>10);
  return x/y;
}

void main()
{
  unsigned x,y;
  __CPROVER_assume(x<10*y && y>10);
  x = foo(x,y);
  assert(x!=y);
}
