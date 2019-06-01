long sasum(long *sx, int n, int incx)
{
  int nincx = n * incx;
  long stemp = 0l;
  int i;
  for (i = 0; incx < 0 ? i >= nincx : i <= nincx; i += incx)
  {
    stemp += sx[i-1];
  }
  return stemp;
}
