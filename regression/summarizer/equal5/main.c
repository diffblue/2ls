void main()
{
  unsigned x=0,y=0;

  while(x<10)
  {
    x++; y++;
  }

  assert(x==y);

  while(y<20)
  {
    x++; y++;
  }

  assert(x==y);
}
