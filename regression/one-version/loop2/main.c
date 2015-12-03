int some_function();

int main()
{
  unsigned int x, y, c;
  
  x=0;
  y=0;
  
  while(some_function())
  {
    if(c)
    {
      x++;
      y++;
    }
  }
  
  assert(x==y);
}
