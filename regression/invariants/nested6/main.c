void main()
{
  int x,y;
  for(x=0;x<10;x++) //y may have any value here
  {
    for(y=0;y<20;y++);
  }

  assert(x==10);
  assert(y==20);
}
