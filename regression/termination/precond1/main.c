unsigned foo(unsigned y)
{
  //__CPROVER_assume(y==0);
  for(unsigned x=0; x<10; x+=y);
  return x;
}

int main(int argc, char** argv)
{
  unsigned y = argc;
  return foo(y-1);
}

