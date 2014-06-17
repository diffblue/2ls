int x = 0;  
int y = 0;

void main()
{

  while(x<10)
    ++x;

  while(y<10)
    ++y;

  assert(x>=0);
  assert(x<=10);
  assert(y>=0);
  assert(y<=10);
}
