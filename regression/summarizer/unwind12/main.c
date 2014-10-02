void main()
{
  int x=0;
  int y;
  do
  {
    y=0;
    do
    {
      y += 3;
    }
    while(y<20);
    assert(y==20); //should fail 
  }
  while(x++<10);
  assert(x==10); //should fail
}
