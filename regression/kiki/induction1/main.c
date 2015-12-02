void main()
{
  int x = 1;  

  while(1)
  {
    if(x==2) x=-x;
    if(x>0) x++;
    if(x==0) assert(0);
    if(-10<=x && x<0) x--;
  }
}
