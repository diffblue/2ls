extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: __VERIFIER_error(); } }

#define N 1000000

int main ( ) {
  int a[N];
  int i = 1;
  while ( i < N ) {
    a[i] = 42;
    i = i + 1;
  }

  int x;
  for ( x = 1 ; x < N ; x++ ) {
    __VERIFIER_assert(  a[x] == 42  );
  }
  __VERIFIER_assert(a[1] == 42);
  return 0;
}
