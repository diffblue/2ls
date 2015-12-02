void main()
{
  for(int x=0;x<10;x++)
  {
    for(int y=0;y<5;y++)
    {
      assert(0<=y && y<=5);
    }
    assert(0<=x && x<=10);
  }
}
