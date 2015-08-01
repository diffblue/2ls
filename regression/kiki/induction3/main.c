void main()
{
  int x = 0, y = 0, z = 0;  

  while(1)
  {
    z = -y;
    y = -x;
    x++;
    assert(x<=z+2);
  }
}
