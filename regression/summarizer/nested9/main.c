void main()
{
  int x=0;
  do
  {
    int y=0;
    while(y<10)
    {
      y++;
    }
    assert(y==10);
  }
  while(++x<10);
  assert(x==10);
}
