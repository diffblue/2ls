#include <assert.h>
#include <stdio.h>
#include <limits.h>

//int encoder () {
int main () {
  int inputBytes = 0;
  int outputBytes = 0;
  int encodedBytes = 0;

  int last = EOF; 
  unsigned char count = 1;
  int current;

  do 
  {
    current = getchar();
    inputBytes += (current == EOF) ? 0 : 1;

    if ((current == last) && (count < 5 /*UCHAR_MAX - 1*/)) 
    {
      ++count;
    } 
    else 
    {
      if (last != EOF)      
      {
	if (count > 1) 
        {
	  putchar(UCHAR_MAX); ++outputBytes;
	  putchar(count); ++outputBytes;
	}
	if (last == UCHAR_MAX) 
        {
	  putchar(UCHAR_MAX); ++outputBytes;
	}
	putchar(last); 
	++outputBytes;
	encodedBytes += count;
      }

      last = current;
      count = 1;
    }
  } 
  while (last != EOF);

  assert(inputBytes != encodedBytes); //should fail
  // assert(outputBytes <= 2 * inputBytes);

  return 0;
}


