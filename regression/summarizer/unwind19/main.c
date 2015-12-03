void main()
{
  int x = 0;  
  int y;

  do
  {
    ++x;
    if(y) continue;
    ++x;
  }
  while(x<10);

  assert(x==10);
}
