int foo(int x, int y)
{
  while(x<10)
  {
    y++;
    x++; 
    y--;
  }
  
  return y;
}

void main()
{
  unsigned x,y;

  x = foo(x,y);

  assert(x==y);
}
