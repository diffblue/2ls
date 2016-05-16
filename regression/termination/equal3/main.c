unsigned foo(unsigned x, unsigned y) 
{ 
  if(x) return y+1;
  return y-1;
}

void main()
{
  unsigned x,y;
  x = foo(x,y);
  assert(x!=y);
}
