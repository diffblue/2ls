void main()
{
  int x;  
  unsigned y;
  x = -10;
  y = 10;

  while(x<10)
    ++x;

  while(y>0)
    --y;

  assert(-10<=x);
  assert(x<=10);
  assert(0<=y);
  assert(y<=10);
}
