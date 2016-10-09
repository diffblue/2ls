#include <assert.h>

int isOdd(int n);
int isEven(int n);

int isOdd(int n) {
  if (n == 0) {
    return 0;
  } else if (n == 1) {
    return 1;
  } else {
    int m=n-1;
    if (m == 0) {
      return 1;
    } else if (m == 1) {
      return 0;
    } else {
      return isOdd(m - 1);
    }
  }
}

int main() {
  int n;
  __CPROVER_assume(n>0);
  int result = isOdd(n);
  int mod = n % 2;
  assert(result < 0 || result == mod);
  return 0;
}
