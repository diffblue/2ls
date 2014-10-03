int foo(int x)
{
  if(x>0) while(1);
  return x;
}

int main(int argc, char** )
{
  int x = argc;
  x = foo(x);  
  assert(x<=0);
}
