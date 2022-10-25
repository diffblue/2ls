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
        n->size = 0;
        for (int i = 0; i < NODE_SIZE; i++)
            n->elems[i] = 0;

        n->next = list;
        list = n;
    }

    for (struct node *n = list; n != NULL; n = n->next) {
        for (int i = 0; i < NODE_SIZE; i++)
            __VERIFIER_assert(n->elems[i] == 0);
    }
}

