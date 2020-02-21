extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: __VERIFIER_error(); } }

#define N 100

int main ( ) {
  int a[N];
  int i = 0;
  while ( i < N - 1 ) {
    a[i] = 42;
    a[i + 1] = 42;
    i = i + 1;
  }
  
  int x;
  for ( x = 0 ; x < N ; x++ ) {
    __VERIFIER_assert(  a[x] == 42  );
  }
  __VERIFIER_assert(a[0] == 42);
  return 0;
}
