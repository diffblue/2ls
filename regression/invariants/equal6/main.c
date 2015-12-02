void main()
{
  unsigned x=0,y=0;

  while(x<10)
  {
    x++; 
    while(y<x) //equality does not hold at loop head
    {
      y++;
    }
  }

  assert(x==y);
}
