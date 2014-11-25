void main()
{
  int x,y;
  for(x=0; x<100; x++)
  {
    for(y=0; y<=x; y++);
  }
  assert(x==100);
  assert(y==100);
}
