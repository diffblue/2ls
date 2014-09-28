int random();

int wcet1 (int n) {
  int i,j;

  j=0;
  i=n;
  if (n>=1) 
    do {
      if (random()){
	  j++;
	  if(j>=n) j=0;
	}
      else {
	j--;
	if(j<=0) j=0;
      }
      
      i--;
    }
    while(i>0);

  return 0;
}
