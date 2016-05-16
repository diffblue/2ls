#include <assert.h>

int global;

int main()
{
  int *p;
  
  p=&global;
  assert(p==&global);
  global=1;
  assert(global==1);
  
  // writing to pointer
  *p=2;
  assert(global==2);  
  
  // reading from pointer
  global=3;
  assert(*p==3);
}
