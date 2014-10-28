void foo(int x)
{
  if(x==1) while(1);
}

void bar()
{
}

int main(int argc, char** argv)
{
  int x = 2;
  if(x==2) foo(argc);
  bar();
  foo(1);
  return 0; //status should be UNKNOWN
}
