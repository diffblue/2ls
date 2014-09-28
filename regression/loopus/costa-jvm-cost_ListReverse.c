#include <stdlib.h>

typedef struct ListReverse {
	int data;
	struct ListReverse *next;
} ListReverse;

ListReverse *reverse(ListReverse *x) {
	ListReverse *result = (ListReverse *)NULL;
	ListReverse *tmp = (ListReverse *)NULL;

	while (x != (ListReverse *)NULL) {
	    tmp = x->next;
	    x->next = result;
	    result = x;
	    x = tmp;
	}

	return result;
}

