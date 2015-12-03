void main()
{
  int x=0;
  do
  {
    int y=0;
    while(y<20)
    {
      y++;
    }
    assert(y==20);
  }
  while(++x<10);
  assert(x==10);
}
