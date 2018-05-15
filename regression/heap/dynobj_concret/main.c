extern void __VERIFIER_error() __attribute__ ((__noreturn__));

extern int __VERIFIER_nondet_int();

#include <stdlib.h>

void exit(int s) {
	_EXIT: goto _EXIT;
}

typedef struct node {
  struct node *n;
} *List;

int main() {
  /* Build a list of the form 1->...->1->0 */
  List t;
  List p = NULL;
  while (__VERIFIER_nondet_int()) {
    t = (List) malloc(sizeof(struct node));
    t->n = p;
    p = t;
  }

  if (p && p->n) {
    List n = p->n;
    List nn = n->n;
    assert(n==nn);
  }
}
