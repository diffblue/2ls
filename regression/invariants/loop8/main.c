void main()
{
  int x = 0;

  while(x<10)
    ++x;

  while(x<20)
    ++x;

  while(x>-10)
    --x;

  assert(-10<=x);
  assert(x<=20);
}
