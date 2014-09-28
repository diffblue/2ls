#include <stdlib.h>

int *arrayReverse(int a[], int length) {
	int l = length;
	int *r = malloc(length * sizeof(int));

	for (int i = l; i > 0; i--) {
		r[l-i] = a[i-1];
	}

	return r;
}
