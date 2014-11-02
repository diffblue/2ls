void foo(int a) 
{ 
  assert(0);
}

int bar(int b) 
{ 
  int x = b;
  assert(b!=9);
  return x;
}

int main(int argc, char** argv)
{
  int x = argc;
  if(x==8) foo(x);
  int y = bar(x);
  assert(y!=10);
  return 0;
}
