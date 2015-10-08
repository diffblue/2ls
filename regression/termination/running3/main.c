/* 
  C version of the lapack library

  http://www.netlib.org/clapack/cblas/sasum.c
  
  run with
  
  ../../../src/summarizer/summarizer main.c --termination --context-sensitive
  
*/

int nondet_int();

int foo(int *sx, int n, int incx) 
{ 
  int nincx = n * incx;
  int stemp=0;
  int i;
  for (i=0; incx < 0 ? i >= nincx : i <= nincx; i += incx) 
  { 
    stemp += sx[i-1];
  }
  return stemp;
}

int bar(int n, int incx) 
{
  int sx[n];
  if(100 <= n && n <= 10000 && 0 < incx && incx <= 1000) 
  {
    int stemp = foo(&sx, n, incx);
  }
  return 0;
}

int main()
{
  int n = nondet_int(), incx = nondet_int(); 
  bar(n,incx);
}
