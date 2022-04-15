extern int __VERIFIER_nondet_int();
#include <assert.h>
#include <stdlib.h>

struct list
{
  int x;
  struct list *n;
};

void main()
{
  struct list *l=NULL;
  while(__VERIFIER_nondet_int())
  {
    struct list *n=malloc(sizeof(struct list));
    n->n=l;
    n->x=1;
    l=n;
  }

  // Jump twice each time
  while(l!=NULL)
  {
    assert(l->x==1);
    l=l->n;
    l=l->n;
  }
}
