#include <stdlib.h>

typedef struct ListReverse {
	int data;
	struct ListReverse *next;
} ListReverse;

ListReverse *listInter(ListReverse *l1, ListReverse *l2) {
	ListReverse *r = (ListReverse *)malloc(sizeof(ListReverse));
	r->next = (ListReverse *)NULL;
	ListReverse *last = r;
	ListReverse *aux = l1;
	while (aux != (ListReverse *)NULL) {
		ListReverse *auxSub = l2;
		while (auxSub != (ListReverse *)NULL && auxSub->data != aux->data)
			auxSub = auxSub->next;
		if (auxSub != (ListReverse *)NULL) {
			ListReverse *node = (ListReverse *)malloc(sizeof(ListReverse));
			node->data = aux->data;
			node->next = (ListReverse *)NULL;
			last->next = node;
			last = node;
		}
		aux = aux->next;
	}
	r = r->next;
	return r;
}

//static int find(ListReverse l,int e){
//	ListReverse aux=l;
//	while (aux!=null && aux.data != e) aux=aux.next;
//	if (aux!=null) return 1;
//	else return 0;
//}
