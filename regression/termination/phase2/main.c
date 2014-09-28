void main()
{
  unsigned char x = 1;  
  unsigned char y = 1;  

  while(x>0) //terminates after overflow of x
  {
    if(y<100) x++;
    y++;
  }
  assert(x==0);
}
