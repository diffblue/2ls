// Source: Ken McMillan: "Lazy Abstraction With Interpolants", CAV 2006

#include "assert.h"

void main() {
    int n = __VERIFIER_nondet_int();
    __VERIFIER_assume(0 <= n && n <= 5);
    int *x = malloc(n * sizeof(int));
    for (int i = 0; i < n; i++) x[i] = 0;
    for (int i = 0; i < n; i++) __VERIFIER_assert(x[i] == 0);
}
