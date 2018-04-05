extern int __VERIFIER_nondet_int();

#include <stdlib.h>

typedef struct node {
    int val;
    struct node *next;
} Node;

int main() {
    Node *p, *list = malloc(sizeof(*list));
    list->next = NULL;
    list->val = 10;
    while (__VERIFIER_nondet_int()) {
        int x;
        __CPROVER_assume(x >= 10 && x <= 20);
        p = malloc(sizeof(*p));
        list->next = p;
        p->next = NULL;
        p->val = x;
        list = p;
    }

    while (1) {
        for (p = list; p!= NULL; p = p->next) {
            assert(p->val <= 20 && p->val >= 10);
            if (p->val < 20) p->val++;
            else p->val /= 2;
        }
    }

}
