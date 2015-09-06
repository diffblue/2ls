void main()
{
  int x = 0;  

  while(x<10)
  {
    ++x;
    assert(0<=x && x<=10);
  }

  assert(x==10);
}
