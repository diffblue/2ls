extern void abort(void);
#include <assert.h>
void reach_error() { assert(0); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } }
extern int __VERIFIER_nondet_int();
#define NULL 0

#define NODE_SIZE 10

struct node {
    int size;
    int elems[NODE_SIZE];
    struct node *next;
};

int main() {
    struct node *list = NULL;

    while (__VERIFIER_nondet_int()) {
        struct node *n = malloc(sizeof(*n));
        n->size = __VERIFIER_nondet_int();
        __CPROVER_assume(n->size >= 0 && n->size < NODE_SIZE);

        // Fill node with numbers between 0 and 100
        for (int i = 0; i < n->size; i++) {
            int val = __VERIFIER_nondet_int();
            __CPROVER_assume(val >= 0 && val <= 100);
            n->elems[i] = val;

        }
        // Fill the rest of the array with zeroes
        for (int i = n->size; i < NODE_SIZE; i++)
            n->elems[i] = 0;

        n->next = list;
        list = n;
    }



    for (struct node *n = list; n != NULL; n = n->next) {
        for (int i = 0; i < 5; i++)
            __VERIFIER_assert(n->elems[i] >= 0 && n->elems[i] <= 100);
    }
}


