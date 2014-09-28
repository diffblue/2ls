#include <stdlib.h>

typedef struct LinkedList {
	int elem;
	struct LinkedList *next;
} LinkedList;

LinkedList *copy(LinkedList *c) {
	LinkedList *cons = (LinkedList *) NULL;
	for (; c != NULL; c = c->next) {
		LinkedList *copyCons = (LinkedList *) malloc(sizeof(LinkedList));
		copyCons->elem = c->elem;
		if (cons != NULL) {
			cons->next = copyCons;
		}
		cons = copyCons;
	}
	return cons;
}
