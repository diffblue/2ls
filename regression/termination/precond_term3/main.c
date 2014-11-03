int foo(int y)
{
  while(1)
  {
    if(y>=1) return y;
  }
}

int main(int argc, char** argv)
{
  return foo(argc);
}

