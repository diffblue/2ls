int foo(int x) 
{ 
  int y = x;
  assert(y>=10);
  return y;
}

int main(int argc, char** argv)
{
  int y = foo(argc);
  assert(y>=15);
  return y;
}
