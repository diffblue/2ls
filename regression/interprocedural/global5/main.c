#include <assert.h>

int x = 0;

void foo()
{
  x = 1;
}

void bar()
{
  foo();
}

int main(int argc, char** argv)
{
  bar();
  assert(x == 1);
}
