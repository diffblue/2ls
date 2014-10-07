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
  //   __CPROVER_assume(argc>10);
  int x = argc;
  if(x>100) x = foo(x);
  else bar(); //unreachable
  return x;
}
