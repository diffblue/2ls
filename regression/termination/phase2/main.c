void main()
{
  unsigned char x = 1;  
  unsigned char y = 1;  
  unsigned char w = 0;  

  while(x>0) //terminates after overflow of x  // -w, -y, -x
  {
    if(y<100) x++;
    y++;
    if(y==0) w++;
  }
  assert(x==0);
}
