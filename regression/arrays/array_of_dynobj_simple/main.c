extern void abort(void);
#include <assert.h>
void reach_error() { assert(0); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } }
extern int __VERIFIER_nondet_int();
#define NULL 0

#define N 100000

int main() {
    int *a[N];

    for (int i = 0; i < N; i++)
    {
        a[i] = malloc(sizeof(int));
    }

    for (int i = 0; i < N; i++)
    {
        __VERIFIER_assert(a[i] != NULL);
    }
}

