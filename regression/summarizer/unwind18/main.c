void main()
{
  int x = 0;  
  int y;

  while(x<10)
  {
    ++x;
    if(y) continue;
    ++x;
  }

  assert(x==10 || x==11);
}
