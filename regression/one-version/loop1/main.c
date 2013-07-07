int some_function();

int main()
{
  unsigned int x, y;
  
  x=0;
  y=0;
  
  while(some_function())
  {
    x++;
    y++;
  }
  
  assert(x==y);
}
