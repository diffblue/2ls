extern int __VERIFIER_nondet_int();
#include <stdlib.h>

typedef struct node {
  int h;
  struct node *n;
} *List;

int main() {
  /* Build a list of the form 1->1->2->1->... */
  List t;
  List p = 0;
  int i = 0;
  while (__VERIFIER_nondet_int()) {
    t = (List) malloc(sizeof(struct node));
    t->h = i == 2 ? 2 : 1;
    t->n = p;
    p = t;
    i++;
  }
  while (p!=0) {
    assert(p->h==1);
    p = p->n;
  }
}

