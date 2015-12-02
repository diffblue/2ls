void foo(int x)
{
  if(x==1) while(1);
}

void bar()
{
}

int main(int argc, char** argv)
{
  int x;
  if(argc==1) foo(argc);
  bar();
  foo(x);
  return 0; //status should be UNKNOWN
}
