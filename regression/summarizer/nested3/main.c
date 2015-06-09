void main()
{
  int x = 0, y = 0;
  for(; x<10; x++)
  {
    for(y=x; y<10; y++);
  }
  assert(x==10);
  assert(y==10);
}
