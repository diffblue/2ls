void main()
{
  int x=0, y=0;
  for(; x<100; x++)
  {
    for(y=0; y<=x; y++);
  }
  assert(x==100);
  assert(y==100);
}
