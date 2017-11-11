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
  struct list *nl1=malloc(sizeof(struct list));
  nl1->x=-1;
  nl1->n=l;
  l=nl1;
  struct list *nl2=malloc(sizeof(struct list));
  nl2->x=-1;
  nl2->n=l;
  l=nl2;
  
  struct list *m=l;
  for(int i=0; m!=NULL; ++i)
  {
    m->x=i;
    m=m->n;
  }

  assert(l->n->x==0);
  assert(l->n->x==1);
  assert(l->x==2);
  assert(l->x==1);
}
