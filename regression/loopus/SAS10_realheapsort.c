//realheapsort
void realheapsort(int N, float t[])
{
  float temp;
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

  //destruction
  
    for (k=0;k<=N-2;k++)
      {
        j = 0; m=0;
        temp = t[N-k-1];
        t[N-k-1]=t[0];
        t[0]=temp;
        while(2*j+1<=N-2-k)
	  {
	    if ((2*j+1==N-2-k) || (t[2*j+1]<t[2*j+2]))
	      m=2*j+1;
	    else
	      m=2*j+2;
            if (t[j]>t[m])
	      {//swap j m
	        temp=t[m];
	        t[m]=t[j];
                t[j]=temp;
	        j=m;
	      }
            else j=N;
	  
	  }
     
      }
  }
}
