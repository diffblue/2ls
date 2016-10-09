#include <assert.h<

int f91(int x) {
  if (x > 100)
    return x-10;
  else {
    return f91(f91(x+11));
  }
}

int main() {
  int x;
  int result = f91(x);
  assert(result == 91 || x > 101 && result == x - 10);
  return 0;
}
