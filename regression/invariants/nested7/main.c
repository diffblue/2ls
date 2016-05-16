void main()
{
  int x=0;
  int y;
  while(x<10)
  {
    y=0;
    do
    {
      y++;
    }
    while(y<10);
    assert(y==10);
    x++;
  }
  assert(x==10);
}
