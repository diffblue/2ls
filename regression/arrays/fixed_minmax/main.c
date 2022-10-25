extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: __VERIFIER_error(); } }
extern int __VERIFIER_nondet_int();

#define N 1000000

int main( ) {
  int a[N];

  for (int i = 0; i < N; i++)
    a[i] = __VERIFIER_nondet_int();

  // Choose random numbers from the array with the min and the max values
  int max = __VERIFIER_nondet_int();
  __CPROVER_assume(max >= 0 && max < N);

  int min = __VERIFIER_nondet_int();
  __CPROVER_assume(min >= 0 && min < N);

  __CPROVER_assume(a[min] < a[max]);

  // Non-determinisically move val from min to max
  int val = a[min];
  while (__VERIFIER_nondet_int())
  {
    if (__VERIFIER_nondet_int())
    {
        if (val < a[max])
            val++;

    }
    else
    {
        if (val > a[min])
            val--;
    }
  }

  // Check that val is between min and max
  __VERIFIER_assert(val >= a[min] && val <= a[max]);

  return 0;
}
