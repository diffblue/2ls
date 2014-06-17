int z;

void doit()
{

  int x;
  unsigned y;
  x=0;
  y=0;
  
  while(x<10 && y<20)
  {
    ++x;
    ++y;
  }
  
  z=x+y;
  assert(z<=50);
}
