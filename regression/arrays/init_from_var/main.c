extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: __VERIFIER_error(); } }
extern int __VERIFIER_nondet_int();

#define N 1000000

int main ( ) {
  int a[N];

  int x = 0;
  while (__VERIFIER_nondet_int())
      x++;

  int i = 0;
  while ( i < N ) {
    a[i] = x;
    i = i + 1;
  }

  for ( i = 0 ; i < N ; i++ ) {
    __VERIFIER_assert(  a[i] == x  );
  }
  return 0;
}
