extern int __VERIFIER_nondet_int();

#define SIZE 1000

int main() {
  int **matrix;
  unsigned m = __VERIFIER_nondet_int();
  unsigned n = __VERIFIER_nondet_int();
  __CPROVER_assume(m <= SIZE && n <= SIZE && m * n <= SIZE);

  int array[SIZE];
  for (int row = 0; row < m; ++row) {
    for (int col = 0; col < n; ++col) {
#ifndef NOBUG
      int index = row * m + col;
#else
      int index = row * n + col;
#endif
      array[index] = matrix[row][col];
    }
  }
  return 0;
}
