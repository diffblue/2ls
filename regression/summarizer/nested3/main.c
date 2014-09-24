void main()
{
  int x,y;
  for(x=0; x<10; x++)
  {
    for(y=x; y<10; y++);
  }
  assert(x==10);
  assert(y==10);
}
