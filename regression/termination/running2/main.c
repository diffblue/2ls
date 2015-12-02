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
//  assert(-(i-(i+incx))>0);
//  assert((signed __CPROVER_bitvector[44])-1 * (signed __CPROVER_bitvector[44])((signed __CPROVER_bitvector[33])i - (signed __CPROVER_bitvector[33])(i+incx)));
  for (i=0; incx < 0 ? i >= nincx : i <= nincx; i += incx);
}

int g(int n, int incx)
{
  __CPROVER_assume(incx >= 0 && incx < 1000);
  __CPROVER_assume(n < 1000 && n > 0);

  f(n,incx);
}

int main()
{
  int n = nondet_int(), incx = nondet_int();
  
  g(n,incx);
  
  return 0;
}
