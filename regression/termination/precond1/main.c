#include <limits.h>

int foo(int y)
{
  int x=0;
  for(; x<10; x+=y);
  return x;
}

int main(int argc, char** argv)
{
  int y = argc;
  return foo(y-1);
}

