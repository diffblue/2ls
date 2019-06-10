extern int __VERIFIER_nondet_int();

#include <stdlib.h>
#include <limits.h>

#define APPEND(l,i) {i->next=l; l=i;}

typedef struct node {
  struct node *next;
  int val;
} Node;

int main() {
  Node *l = NULL;
  int min = INT_MAX;

  while (__VERIFIER_nondet_int()) {
    Node *p = malloc(sizeof(*p));
    p->val = __VERIFIER_nondet_int();
    APPEND(l, p)

    if (min > p->val)
      min = p->val;
  }

  for (Node *i = l; i != NULL; i = i->next)
    assert(i->val >= min);
}
