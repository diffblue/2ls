#include <stdlib.h>

typedef struct Polynomial {
    int deg;
    int coefs[11];
} Polynomial;

Polynomial *copy(Polynomial *this) {
	Polynomial *copy = (Polynomial *)malloc(sizeof(Polynomial));
	copy->deg = this->deg;
	int i;
	for (i = 0; (i <= this->deg && i <= 10); i++)
		copy->coefs[i] = this->coefs[i];
	return copy;
}
