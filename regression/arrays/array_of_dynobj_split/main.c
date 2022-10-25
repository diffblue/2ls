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
    struct item *neg[N];
    struct item *pos[N];

    int n = 0;
    int p = 0;
    while (p < N && n < N)
    {
        int data = __VERIFIER_nondet_int();;

        if (data >= 0 && p < N)
        {
            pos[p] = malloc(sizeof(struct item));
            pos[p]->data = data;
            p++;
        }
        else if (data < 0 && n < N)
        {
            neg[n] = malloc(sizeof(struct item));
            neg[n]->data = data;
            n++;
        }
    }

    for (int i = 0; i < n; i++)
    {
        __VERIFIER_assert(neg[i]->data < 0);
    }

    for (int i = 0; i < p; i++)
    {
        __VERIFIER_assert(pos[i]->data >= 0);
    }
}
