extern void abort(void);
#include <assert.h>
void reach_error() { assert(0); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } }
extern int __VERIFIER_nondet_int();
#define NULL 0

#define N 100000

struct item {
    int data;
};

int main()
{
    struct item *array[N];

    for (int i = 0; i < N; i++)
    {
        int data = __VERIFIER_nondet_int();
        __VERIFIER_assume(data >= 0 && data <= 10);

        struct item *item = malloc(sizeof(struct item));
        item->data = data;
        array[i] = item;
    }

    for (int i = 0; i < N; i++)
    {
        __VERIFIER_assert(array[i] != NULL);
        __VERIFIER_assert(array[i]->data >= 0 && array[i]->data <= 10);
    }
}
