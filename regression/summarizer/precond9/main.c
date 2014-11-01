int foo(int a) 
{ 
  assert(a!=10);
  return a;
}

int bar(int b) 
{ 
  assert(b!=11);
  return b;
}

int main(int argc, char** argv)
{
  int x = foo(argc);
  int y = bar(x);
  assert(y!=12);
}
