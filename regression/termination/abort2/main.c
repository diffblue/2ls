void bar()
{
  while(1);
}

int foo(int x)
{
  return x;
}

int main(int argc, char** argv)
{
  int x = argc;
  if(x>=1) x = foo(x);
  else bar(); //unreachable
  return x;
}
