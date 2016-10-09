#include <assert.h>

struct l_in {
  int x;
};

struct l_out {
  int x;
};

struct l_out B(struct l_in b_in) {
  int x=b_in.x;
  if(x<10) {
    x++;
    struct l_in a_in;
    a_in.x = x;
    return B(a_in);
  }
  struct l_out b_out;
  b_out.x = x;
  return b_out;
}

void main() {
  int x=0;
  struct l_in b_in;
  b_in.x = x;
  struct l_out b_out;
  b_out = B(b_in);
  x = b_out.x;
  assert(x==10);
}
