void main()
{
  int x;
  int y;
  x=0;
  y=0;
  
  while(x<10 && y<20)
  {
    ++x;
    ++y;
  }
  
  int z=x+y;

  assert(z>=0);
  assert(z<=30);
}
