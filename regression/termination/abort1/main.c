int foo(int x)
{
  int y;
  if(x<1) while(1) y++;
  return x;
}

int main(int argc, char** argv)
{
  int x = argc;
  x = foo(x);  
  assert(x>=1);
  return x;
}
