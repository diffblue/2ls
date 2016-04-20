void main()
{
  int x=0;
  int y;
  while(x++<10)
  {
    y=0;
    while(y<20)
    {
      y += 3;
    }
    assert(y==20); //should fail
  }
  assert(x==10); //should fail
}
