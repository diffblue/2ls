extern void __VERIFIER_error() __attribute__ ((__noreturn__));

extern int __VERIFIER_nondet_int();

#include <stdlib.h>

void exit(int s) {
	_EXIT: goto _EXIT;
}

typedef struct node {
  int h;
  struct node *n;
} *List;

int main() {
  /* Build a list of the form 1->...->1->0 */
  List a = (List) malloc(sizeof(struct node));
  if (a == 0) exit(1);
  a->n = 0;
  List t;
  List p = a;
  while (__VERIFIER_nondet_int()) {
    t = (List) malloc(sizeof(struct node));
    if (t == 0) exit(1);
    t->n = 0;
    p->n = t;
    p = p->n;
  }
  p = a;
  while (p!=0) {
    t = p->n;
    free(p);
    p = t;
  }
  return 0;
}

