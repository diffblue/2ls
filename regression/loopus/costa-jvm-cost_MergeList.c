#include <stdlib.h>
#include <stdio.h>

typedef struct MergeList {
	int head;
	struct MergeList *tail;
} MergeList;

MergeList *merge(MergeList *this, MergeList *other) {
	//	if (other == (MergeList *)NULL) return this;
	//	else if (this->head <= other->head)
	//		if (this->tail != (MergeList *)NULL) return _construct(this->head, merge(this->tail, other));
	//		else return _construct(this->head, other);
	//	else return _construct(other->head, merge(this, other->tail));

	if (other == (MergeList *)NULL)
		return this; //_construct(this->head, this->tail);
	if (this == (MergeList *)NULL)
		return other; //_construct(other->head, other->tail);

	MergeList *result = (MergeList *)NULL;
	MergeList *curList = this;
	MergeList *otherList = other;
	MergeList *tmp, *last;
	while (curList != (MergeList *)NULL && otherList != (MergeList *)NULL) {
		if (curList->head <= otherList->head) {
			printf("merge in %d\n", curList->head);
			MergeList *newl = curList; //_construct(curList->head, otherList);
			if (result != (MergeList *)NULL) {
				printf("after %d\n", last->head);
				last->tail = newl;
			}
			else
				result = curList;
			last = newl;
			curList = curList->tail;
		}
		else {
//			printf("switch %d with %d\n", curList->head, otherList->head);
			printf("merge in %d\n", otherList->head);
			MergeList *newl = otherList; //_construct(curList->head, otherList);
			if (result != (MergeList *)NULL) {
				printf("after %d\n", last->head);
				last->tail = newl;
			}
			else
				result = otherList;
			last = newl;
			otherList = otherList->tail;
		}
	}
	while (otherList != (MergeList *)NULL) {
		printf("merge in %d\n", otherList->head);
		printf("after %d\n", last->head);
		last->tail = otherList;
		last = otherList;
		otherList = otherList->tail;
	}
	while (curList != (MergeList *)NULL) {
		printf("merge in %d\n", curList->head);
		printf("after %d\n", last->head);
		last->tail = curList;
		last = curList;
		curList = curList->tail;
	}
	return result;
}

//MergeList *_construct(int head, MergeList *tail) {
//	MergeList *this = (MergeList *)malloc(sizeof(MergeList));
//	this->head = head;
//	this->tail = tail;
//	return this;
//}
//
//MergeList *_append(MergeList *this, MergeList *other) {
//	if (this->tail == (MergeList *)NULL) return _construct(this->head, other);
//	else return _construct(this->head, _append(this->tail, other));
//}
//
//MergeList *_reverseAcc(MergeList *this, MergeList *acc) {
//	if (this->tail == (MergeList *)NULL) return _construct(this->head, acc);
//	else return _reverseAcc(this->tail, _construct(this->head, acc));
//}
//
//MergeList *_reverse(MergeList *this) {
//	if (this->tail == (MergeList *)NULL) return this;
//	else return _append(_reverse(this->tail), _construct(this->head, (MergeList *)NULL));
//}

//int main() {
//	MergeList ml2 = {3, 0};
//	MergeList ml1 = {1, &ml2};
//
//	MergeList ol2 = {2, 0};
//	MergeList ol1 = {0, &ol2};
//
////	MergeList alone = {3, 0};
//	MergeList *l = merge(&ml2, &ol1);
////	MergeList *l = merge(&ol1, &alone);
//	while (l != (MergeList *)NULL) {
//		printf("%d ", l->head);
//		l = l->tail;
//	}
//}
