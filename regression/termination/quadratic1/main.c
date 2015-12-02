void main()
{
  int x = 1, y = 3;
  while(x>0)
  {
    x = x + y;
    y--;
  }
  assert(x>y);
}
