void main()
{
  int x = 1;
  int y = 1;

  while(x>0)
  {
    if(y<10) x++;
    else x--;
    if(y<100) y++;
  }
  assert(x==0);
}
