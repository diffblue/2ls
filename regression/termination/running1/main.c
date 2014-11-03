/* 
  C version of the lapack library

  http://www.netlib.org/clapack/cblas/sasum.c
  
  run with
  
  ../../../src/summarizer/summarizer main.c --termination --context-sensitive
  
*/

int nondet_int();

int f(int n, int incx)
{
  int  nincx = n * incx;
  int i;
  for (i=0; incx < 0 ? i >= nincx : i <= nincx; i += incx);
}

int main()
{

  int n =nondet_int(), incx=nondet_int();
  
  __CPROVER_assume(incx > 0 && incx < 1000);
  __CPROVER_assume(n < 1000 && n > 0);

/*
  int n=10;
  int incx=20;
 */
  f(n, incx);
  return 0;

}
