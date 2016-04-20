int foo(int x)
{
  if(x<1) while(1);
  return x;
}

int main(int argc, char** argv)
{
  int x = argc;
  x = foo(x);  
  assert(x>=1);
  return x;
}
