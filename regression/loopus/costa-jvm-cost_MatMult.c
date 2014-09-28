#include <stdlib.h>
//#include <stdio.h>

int **multiply(int la, int lb, int A[la][lb], int B[lb][la]) {
	int c = lb;  //A.length
	//int r = A[0].length;
	int r = la;
	int **C = malloc(sizeof(int *) * r); //[r][c]
	int i, j, k;

	for (i=0; i < r; i++) {
		C[i] = malloc(sizeof(int) * c);
		for (j=0; j < c; j++) {
			C[i][j] = 0;
			for (k=0; k < c; k++) {
				C[i][j] = C[i][j] + (A[i][k] * B[k][j]);
			}
		}
	}
	return C;
}

//int main() {
//	int A[2][3] = {{3, 2, 1}, {1, 0, 2}};
//	int B[3][2] = {{1, 2}, {0, 1}, {4, 0}};
//	int **C = multiply(2, 3, A, B);
//	int i, j;
//	for (i=0; i < 2; i++) {
//		for (j=0; j < 2; j++) {
//			printf("%d ", C[i][j]);
//		}
//		printf("\n");
//	}
//}
