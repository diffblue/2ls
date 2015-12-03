#define N 10

int foo(int *A)
{
  int i;
  A[9] = 0;
  for (i = 0; i<N; i++) {
    A[i]=i;
  }
}

int main(void) {
  int A[N];

  foo(A);

  int X[N+1];

  foo(X);
  
  int i;
  for (i = 0; i<N; i++) {
    A[i]=i;
  }
}
