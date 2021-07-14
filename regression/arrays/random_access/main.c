extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: __VERIFIER_error(); } }
extern int __VERIFIER_nondet_int();
extern void __VERIFIER_assume(int);

#define N 10

int main ( ) {
  int a[N];
  int i = 0;
  while ( i < N ) {
    a[i] = 0;
    i = i + 1;
  }

  int x;
  while (__VERIFIER_nondet_int()) {
      x = __VERIFIER_nondet_int();
      if (x >= 0 && x <= N)
          a[x] = x;
  }

  for (i = 0; i < N; i++)
      __VERIFIER_assert(a[i] < N);
  return 0;
}

