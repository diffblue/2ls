#define N 10

int main(void) {
  int A[N];
  int i;

  for (i = 0; A[i] != 0; i++) {
    if (i >= N-1) {
      break;
    }
  }

  assert(i < N);
}
