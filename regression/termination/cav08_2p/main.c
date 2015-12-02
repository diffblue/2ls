/* 
  Example from Cook et al, CAV 2008
*/

#define DWORD int
#define UINT unsigned
#define BYTE unsigned char
#define HIWORD(x) ((x)>>16)
#define LOWORD(x) (x)
#define min(x,y) ((x)>(y) ? (y) : (x))

int nondet_int();

void f(int cbSrcLength, int cbHeader, int nBlockAlignment, DWORD *pbSrc, DWORD *pbDst, int* step)
{
//  __CPROVER_assume(cbSrcLength < cbHeader || nBlockAlignment > 0 && cbHeader > 0); // precondition for termination

  while (cbSrcLength >= cbHeader) 
  {
    DWORD dwHeader;
    UINT cbBlockLength;
    cbBlockLength = (UINT)min(cbSrcLength, nBlockAlignment);
    cbSrcLength -= cbBlockLength;
    cbBlockLength -= cbHeader;
/*    dwHeader = *(DWORD *)pbSrc; // dwHeader = *(DWORD HUGE_T *)pbSrc;
    pbSrc += sizeof(DWORD);
    int nPredSample = (int)(short)LOWORD(dwHeader);
    int nStepIndex = (int)(BYTE)HIWORD(dwHeader);
    if( !imaadpcmValidStepIndex(nStepIndex) ) return 0;
    *pbDst++ = (BYTE)((nPredSample >> 8) + 128); */
    while (cbBlockLength--) 
    {
      /*     DWORD bSample = *pbSrc++;
      DWORD nEncSample = (bSample & (BYTE)0x0F);
      int nSz = step[nStepIndex];
      nPredSample =
	imaadpcmSampleDecode(nEncSample, nPredSample, nSz);
      nStepIndex =
	imaadpcmNextStepIndex(nEncSample, nStepIndex);
      *pbDst++ = (BYTE)((nPredSample >> 8) + 128);
      nEncSample = (bSample >> 4);
      nSz = step[nStepIndex];
      nPredSample =
	imaadpcmSampleDecode(nEncSample, nPredSample, nSz);
      nStepIndex =
	imaadpcmNextStepIndex(nEncSample, nStepIndex);
      *pbDst++ = (BYTE)((nPredSample >> 8) + 128);*/
    }
  }
}

int main()
{
  int cbSrcLength = nondet_int();
  int cbHeader = nondet_int();
  int nBlockAlignment = nondet_int();
  DWORD *pbSrc, *pbDst;
  int *step;
  
  f(cbSrcLength, cbHeader, nBlockAlignment, pbSrc, pbSrc, step);

  return 0;
}
