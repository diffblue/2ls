void main()
{
  unsigned char x = 1;  
  unsigned char y = 1;  

  while(x>0) //does not terminate
  {
    if(x<100) x++;
    y++;
  }
  assert(x==0);
}
