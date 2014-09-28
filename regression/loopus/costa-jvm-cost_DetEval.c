/*

This Program is taken from the following site (without permission) solely for the experimentation of cost analysis of practial java programs

http://www.physics.unlv.edu/~pang/cp2_j.html

 */
///////////////////////////////////////////////////////////////////////////
//                                                                       //
// Program file name: Det.java                                           //
//                                                                       //
// Tao Pang 2006                                                       //
//                                                                       //
// Last modified: January 18, 2006                                       //
//                                                                       //
// (1) This Java program is part of the book, "An Introduction to        //
//     Computational Physics, 2nd Edition," written by Tao Pang and      //
//     published by Cambridge University Press on January 19, 2006.      //
//                                                                       //
// (2) No warranties, express or implied, are made for this program.     //
//                                                                       //
///////////////////////////////////////////////////////////////////////////

#include <stdio.h>
#include <stdlib.h>
#include <math.h>

//double det(int la, double a[la][la]);
//void gaussian(int length, double a[length][length], int index[length]);

// An example of evaluating the determinant of a matrix
// via the partial-pivoting Gaussian elimination.

//int main(int argc, const char *argv[]) {
//	double a[][5] = {{ 1, -3,  2, -1, -2},
//			{-2,  2, -1,  2,  3},
//			{ 3, -3, -2,  1, -1},
//			{ 1, -2,  1, -3,  2},
//			{-3, -1,  2,  1, -3}};
void det(int la, double a[la][la]) {
	int i,j,l;
	//	double d = det(5, a);
	int n = la;
	int index[la];

	// Transform the matrix into an upper triangle
	//	gaussian(n, a, index);
	double c[la];

	// Initialize the index
	for (i=0; i<n; ++i) index[i] = i;

	// Find the rescaling factors, one from each row
	for (i=0; i<n; ++i) {
		double c1 = 0;
		for (j=0; j<n; ++j) {
			double c0 = fabs(a[i][j]);
			if (c0 > c1) c1 = c0;
		}
		c[i] = c1;
	}

	// Search the pivoting element from each column
	int k = 0;
	for (j=0; j<n-1; ++j) {
		double pi1 = 0;
		for (i=j; i<n; ++i) {
			double pi0 = fabs(a[index[i]][j]);
			pi0 /= c[index[i]];
			if (pi0 > pi1) {
				pi1 = pi0;
				k = i;
			}
		}

		// Interchange rows according to the pivoting order
		int itmp = index[j];
		index[j] = index[k];
		index[k] = itmp;
		for (i=j+1; i<n; ++i) {
			double pj = a[index[i]][j]/a[index[j]][j];

			// Record pivoting ratios below the diagonal
			a[index[i]][j] = pj;

			// Modify other elements accordingly
			for (l=j+1; l<n; ++l)
				a[index[i]][l] -= pj*a[index[j]][l];
		}
	}

	// Take the product of the diagonal elements
	double d = 1;
	for (i=0; i<n; ++i) d = d*a[index[i]][i];

	// Find the sign of the determinant
	int sgn = 1;
	for (i=0; i<n; ++i) {
		if ((i < index[i]) || (i > index[i])) {
			sgn = -sgn;
			int j = index[i];
			index[i] = index[j];
			index[j] = j;
		}
	}
	d = sgn*d;

	printf("The determinant is: %f\n", d);
}

// Method to evaluate the determinant of a matrix.

//double det(int la, double a[la][la]) {
//	int n = la;
//	int *index = malloc(n * sizeof(int));
//
//	// Transform the matrix into an upper triangle
//	gaussian(n, a, index);
//
//	// Take the product of the diagonal elements
//	double d = 1;
//	for (i=0; i<n; ++i) d = d*a[index[i]][i];
//
//	// Find the sign of the determinant
//	int sgn = 1;
//	for (i=0; i<n; ++i) {
//		if ((i < index[i]) || (i > index[i])) {
//			sgn = -sgn;
//			int j = index[i];
//			index[i] = index[j];
//			index[j] = j;
//		}
//	}
//	return sgn*d;
//}

// Method to carry out the partial-pivoting Gaussian
// elimination.  Here index[] stores pivoting order.

//void gaussian(int lindex, double a[lindex][lindex],
//		int index[lindex]) {
//	int n = lindex;
//	double *c = malloc(n * sizeof(double));
//
//	// Initialize the index
//	for (i=0; i<n; ++i) index[i] = i;
//
//	// Find the rescaling factors, one from each row
//	for (i=0; i<n; ++i) {
//		double c1 = 0;
//		for (j=0; j<n; ++j) {
//			double c0 = fabs(a[i][j]);
//			if (c0 > c1) c1 = c0;
//		}
//		c[i] = c1;
//	}
//
//	// Search the pivoting element from each column
//	int k = 0;
//	for (j=0; j<n-1; ++j) {
//		double pi1 = 0;
//		for (i=j; i<n; ++i) {
//			double pi0 = fabs(a[index[i]][j]);
//			pi0 /= c[index[i]];
//			if (pi0 > pi1) {
//				pi1 = pi0;
//				k = i;
//			}
//		}
//
//		// Interchange rows according to the pivoting order
//		int itmp = index[j];
//		index[j] = index[k];
//		index[k] = itmp;
//		for (i=j+1; i<n; ++i) {
//			double pj = a[index[i]][j]/a[index[j]][j];
//
//			// Record pivoting ratios below the diagonal
//			a[index[i]][j] = pj;
//
//			// Modify other elements accordingly
//			for (l=j+1; l<n; ++l)
//				a[index[i]][l] -= pj*a[index[j]][l];
//		}
//	}
//}
