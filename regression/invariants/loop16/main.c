
void main()
{
  int x = 0;  
  int y = 0;

  do
  {
    ++x;
  }
  while(x<10);

  do 
  {
    ++y;
  }
  while(y<10);

  assert(x==10);
  assert(y==10);
}

