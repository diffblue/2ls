//realheapsort - contruction only
// avec aspic -delay 5
void realheapsort_step1( float t[], float temp, int N)
{
  int k,j,m;
  if(N > 2){
  //construction
    for (k=1;k<=N-1;k++)
      {
        j=k;
        // t[pere j] > t[j]
        while ((j>0) && (t[(j+1)/2-1]>t[j]))
	  {
	    //swap j avec pere j puis j<-pere j
            temp = t[j];
	    t[j] = t[(j+1)/2-1];
	    t[(j+1)/2-1] = temp;
	    j = (j+1)/2-1;
	  }
      }
  }
}
