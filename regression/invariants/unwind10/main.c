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
    while(y<20);
    assert(y==20);
  }
  while(++x<10);
  assert(x==10);
}
