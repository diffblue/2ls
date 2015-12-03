_Bool some_function();

void f(int x, int y)
{
  while(some_function())
  {
    x++;
    y++;
  }

  assert(x==y);
}

void main()
{
  int x,y;
  f(x, y);
}
