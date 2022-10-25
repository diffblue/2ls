extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: __VERIFIER_error(); } }
extern int __VERIFIER_nondet_int();

#define N 1000000

int main( ) {
  int a[N];
  int max = 0;

  for (int i = 0; i < N; i++)
    a[i] = __VERIFIER_nondet_int();

  for (int i = 0; i < N ; i++ ) {
    if ( a[i] > max ) {
      max = a[i];
    }
  }

  int x;
  for ( x = 0 ; x < N ; x++ ) {
    __VERIFIER_assert(  a[x] <= max  );
  }
  return 0;
}
