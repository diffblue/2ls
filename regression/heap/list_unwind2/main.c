#include <assert.h>
#include <stdlib.h>

struct list
{
  int x;
  struct list *n;
};

void main()
{
  struct list *l;
  for(int i=0; i<2; ++i)
  {
    struct list *nl=malloc(sizeof(struct list));
    nl->x=i;
    nl->n=l;
    l=nl;
  }
  assert(l->n->x==1);
  assert(l->x==1);
}
