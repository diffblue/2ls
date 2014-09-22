void main()
{
  int x = 0;  
  int y = 0;  

  while(x<10)
  {
    ++x;
    ++y;
  }

  while(y<30)
  {
    ++y;
    ++x;
  }

  assert(x==30 && y==30);
}
