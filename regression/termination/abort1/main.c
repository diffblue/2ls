int foo(int x)
{
  if(x>100) while(1);
  return x;
}

int main(int argc, char** argv)
{
  int x = argc;
  x = foo(x);  
  assert(x<=100);
  return x;
}
