#include <stdlib.h>
#include <assert.h>

extern int __VERIFIER_nondet_int(void);

struct list{
	struct list* next;
};

int main()
{
	struct list *p,*q;
	p = malloc(sizeof(struct list));
	q = malloc(sizeof(struct list));
	
	p->next = malloc(sizeof(struct list));
	q->next = malloc(sizeof(struct list));
	p = q;

	while(__VERIFIER_nondet_int) {
		q = p->next;
		q->next = malloc(sizeof(struct list));
		assert(q->next != NULL);
		p = q;
	}

	return 1;
}
