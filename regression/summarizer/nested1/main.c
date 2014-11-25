void main()
{
  int x,y;
  for(x=0;x<100;x++)
  {
    for(y=0;y<200;y++);
  }

  assert(x==100);
  assert(y==200);
}
