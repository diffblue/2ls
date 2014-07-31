#include <assert.h>

#define LENGTH 1024

int array[LENGTH];

void initialise (int base)
{
  for (int i = 0; i < LENGTH; ++i) {
    array[i] = i;
  }

  return;
}

int main (void)
{
  int x;

  initialise(x);

  assert(array[23] == 23);

  return 1;
}

