#include <assert.h>

int inc(int x) {
  if(x<10) {
    return inc(x+1);
  }
  return x;
}

void main() {
  int x=0;
  x=inc(x);
  assert(x==10);
}
