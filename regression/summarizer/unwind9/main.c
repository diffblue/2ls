void main()
{
  int x=0;
  int y;
  while(x<10)
  {
    y=-1;
    do
    {
      y++;
    }
    while(y<x);
    assert(y>=x); 
    x++;
  }
  assert(x==10);
}
