void main()
{
  int x = 10;  

  while(x>0)
  {
    --x;
    assert(x>=0);
  }

  assert(x==0);
}
