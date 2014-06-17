void main()
{
  int x=0;
  int y=0;
  for(;x<10;x++)
  {
    for(y=0;y<20;y++);
  }

  assert(0<=x && x<=10);
  assert(0<=y && y<=20);
}
