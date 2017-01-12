#include<assert.h>
int f(int x) {
  return 2*x;
}

int g(int x) {
  int y = x;
  while (x--) {
    y++;
  }
  return y;
}

int main(void) {
  int x;
  //assert(f(5) == g(5));
  __CPROVER_assume(x>=0 && x<=2);
  assert(f(x) == g(x));
}
