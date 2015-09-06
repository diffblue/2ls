void main()
{
  int x = 0;  
  int y;

  while(y)
  {
    ++x;
  }

  assert(x==0); //should hold, but requires y==0 => x==0
}
