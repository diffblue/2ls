#include <stdlib.h>

int *concat(int a[], int b[], int lengthA, int lengthB) {
	int   l1 = lengthA;
	int   l2 = l1 + lengthB;
	int *r = malloc(sizeof(int) * l2);
	int i = 0;
	for (i=0; i < l1; i++){
		r[i] = a[i];
	}

	for (i=l1; i < l2; i++){
		r[i] = b[i];
	}

	return r;
}
