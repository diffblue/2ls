#include <stdlib.h>

int main() {
  int *a = malloc(sizeof(int));
  *a = __VERIFIER_nondet_int();

  int **b = malloc(sizeof(int *));
  *b = a;

#ifdef INVALID_FREE
  free(b);
  free(*b);
#else
  free(*b);
  free(b);
#endif
}
