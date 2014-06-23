
void main()
{
  int x = 0;  
  int y = 0;

  while(x<10)
    ++x;

  while(y<10)
    ++y;

  assert(x==10);
  assert(y==10);
}
