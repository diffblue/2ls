void main()
{
  int x = 0, y = 100;  

  while(x<100 && y>0)
  {
    int c;
    if(c) ++x;
    else --y;
    assert(0<=x);
    assert(x<=100);
    assert(y>=0);
    assert(y<=100);
  }
}

