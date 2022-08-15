int foo(int x)
{
  int y;
  if(x<0) while(1) y++;
  return x;
}

int main(int argc, char** argv)
{
  int x = argc;
  x = foo(x);
  assert(x>=0);
  return x;
}
