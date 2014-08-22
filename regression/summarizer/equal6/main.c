void main()
{
  unsigned x=0,y=0;

  while(x<10)
  {
    x++; 
    while(y<x)
    {
      y++;
    }
  }

  assert(x==y);
}
