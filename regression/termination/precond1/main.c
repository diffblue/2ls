int foo(int y)
{
  for(int x=0; x<10; x+=y);
  return x;
}

int main(int argc, char** argv)
{
  return foo(argc);
}

