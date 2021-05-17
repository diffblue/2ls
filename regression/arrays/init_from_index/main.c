extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern void __VERIFIER_assume(int);
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: __VERIFIER_error(); } }
extern int __VERIFIER_nondet_int();

#define n 1000000

int main()
{
  int i;
  int j=__VERIFIER_nondet_int();
  int a[n];

  __VERIFIER_assume(j>0 && j < 100);

  for(i=0;i<n;i++) {
    int k=__VERIFIER_nondet_int();
    __VERIFIER_assume(k>0 && k < 100);
    a[i]=i+j+k;
  }

  for(i=0;i<n;i++)
    __VERIFIER_assert(a[i]>=(i+2));
  return 0;
}
