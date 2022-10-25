extern void abort(void);
#include <assert.h>
void reach_error() { assert(0); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } }
extern int __VERIFIER_nondet_int();
#define NULL 0

#define N 10

struct item {
    int data;
    struct item *next;
};

int main ()
{
    struct item *array[N];
    int i = 0;

    for (i = 0; i < N; i++)
    {
        array[i] = NULL;
    }

    for (i = 0; i < 3 * N; i++)
    {
        int j = i % N;

        struct item *new_item = malloc(sizeof(struct item));
        new_item->data = i;
        new_item->next = array[j];
        array[j] = new_item;
    }

    for (i = 0; i < N; i++)
    {
        struct item *item = array[i];
        while (item)
        {
             __VERIFIER_assert(item->data >= 0);
            item = item->next;
        }
    }

    return 0;
}
