void main()
{
  for(int x=10; x!=0; x--)
  {
    for(int y=0; y!=10; y++)
    {
      assert(y<=10);
    }
    assert(y==10);
    assert(x>=0);
  }

  assert(x==0);
}
