extern void abort(void);
#include <assert.h>
void reach_error() { assert(0); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } }
extern int __VERIFIER_nondet_int();
#define NULL 0

#define NODE_SIZE 10

struct obj {
    int array[NODE_SIZE];
};

int main() {
    struct obj *o = malloc(sizeof(*o));
    for (int i = 0; i < NODE_SIZE; i++)
        o->array[i] = 0;

    for (int i = 0; i < NODE_SIZE; i++)
        __VERIFIER_assert(o->array[i] == 0);
}

