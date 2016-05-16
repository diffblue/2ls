void main()
{
  unsigned char x = 1;  
  unsigned char y = 1;  

  while(x>0) //does not terminate
  {
    y++;
  }
  assert(x==0);
}
