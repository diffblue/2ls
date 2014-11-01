void foo(int a) 
{ 
  assert(a!=10);
}

void bar(int b) 
{ 
  assert(b!=11);
}

int main(int argc, char** argv)
{
  foo(argc);
  bar(argc);
  assert(argc!=12);
  return 0;
}
