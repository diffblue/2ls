void foo()
{
  while(1);
}

void bar()
{
}

int main(int argc, char** argv)
{
  if(argc>=0) foo();
  bar();
  return 0; //status should be NO
}
