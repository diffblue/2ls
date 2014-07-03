#define SIZE 1024

int main(void) {
  int A[SIZE];
  int i;

  for (i = 0; i < SIZE; i++) {
    A[i] = i;
  }

  assert(A[SIZE-1] == SIZE-1); //currently out of reach to prove that without unrolling
}
