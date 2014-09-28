//realheapsort - destruction only
//aspic - delay 3 nécessaire, et pas de -nomu dans rank
// on trouve 
void realheapsort_step2(float t[], float temp,
  int N)
{
  
  int k,j,m;
  if(N > 2){
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
  
