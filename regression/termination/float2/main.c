#include <assert.h>

int main(int argc, char** argv)
{
  float x = 10.0;

  while(x>0)
  {
    x *= 0.1;
  }
  assert(x>=0.0);
  return 0;
}
