void main()
{
  int x = 0;  
  int y = 0;  

  while(x<10)
  {
    ++x;
    ++y;
  }

  while(y<20)
  {
    ++y;
    ++x;
  }

  assert(x==20 && y==20);
}
