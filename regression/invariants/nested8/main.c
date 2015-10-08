void main()
{
  int x=0;
  do
  {
    int y=0;
    do
    {
      y++;
    }
    while(y<10);
    assert(y==10);
  }
  while(++x<10);
  assert(x==10);
}
