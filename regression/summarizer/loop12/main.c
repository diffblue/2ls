void main()
{
  int x = 0;  
  int y;

  while(y)
  {
    int z;
    y = z;
    ++x;
  }

  assert(x==0);
}
