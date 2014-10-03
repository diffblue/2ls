void main()
{
  int x=0;
  while(x<10)
  {
    x++;
    assert(x<10);
  }
  assert(x==10);
}
