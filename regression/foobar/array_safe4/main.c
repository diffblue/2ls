#define N 10

int foo(int *A)
{
  int i;
  A[N-1] = 0;
  for (i = 0; A[i] != 0; i++) {
  }
  assert(i <= N);
}

int main(void) {
  int A[N];

  foo(A);
}
