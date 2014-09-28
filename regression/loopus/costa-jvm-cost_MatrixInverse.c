/*

This Program is taken from the following site (without permission) solely for the experimentation of cost analysis of practial java programs

http://www.physics.unlv.edu/~pang/cp2_j.html

 */
///////////////////////////////////////////////////////////////////////////
//                                                                       //
// Program file name: Inverse.java                                       //
//                                                                       //
//  Tao Pang 2006                                                       //
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

// An example of performing matrix inversion through the
// partial-pivoting Gaussian elimination.

#include <stdio.h>
#include <math.h>

//int main(int argc, const char *argv[]) {
//	double a[][3]= {{ 100,  100,  100},
//			{-100,  300, -100},
//			{-100, -100,  300}};
//	int n = 3;
void inverse(int la, double a[la][la]) {
	int i, j, l;
	//    double d[][] = invert(a);
	int n = la;
	double x[la][la];
	double b[la][la];
	int index[la];
	for (i=0; i<n; ++i) b[i][i] = 1;

	// Transform the matrix into an upper triangle
	//    gaussian(a, index);
	// Method to carry out the partial-pivoting Gaussian
	// elimination.  Here index[] stores pivoting order.
	double c[n];

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

	// Update the matrix b[i][j] with the ratios stored
	for (i=0; i<n-1; ++i)
		for (j=i+1; j<n; ++j)
			for (k=0; k<n; ++k)
				b[index[j]][k] -= a[index[j]][i]*b[index[i]][k];

	// Perform backward substitutions
	for (i=0; i<n; ++i) {
		x[n-1][i] = b[index[n-1]][i]/a[index[n-1]][n-1];
		for (j=n-2; j>=0; --j) {
			x[j][i] = b[index[j]][i];
			for (k=j+1; k<n; ++k) {
				x[j][i] -= a[index[j]][k]*x[k][i];
			}
			x[j][i] /= a[index[j]][j];
		}
	}

	for (i=0; i<n; ++i)
		for (j=0; j<n; ++j)
			printf("%f\n", x[i][j]);
}

