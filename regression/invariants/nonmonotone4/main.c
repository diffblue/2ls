void main()
{
  for(int x=10; x!=0; x--)
  {
    for(int y=10; y!=0; y--)
    {
      assert(y>=0);
    }
    assert(y==0);
    assert(x>=0);
  }

  assert(x==0);
}
