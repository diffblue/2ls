int random();

void random2d(int N) {
  int x;
  int y;
  int i;
  int r;


  x=0;
  y=0;
  i=0;
  while (i<N) {
    i=i+1;
    r=random(); 
    if (r>=0 && r<=3) {
    	if (r==0) x=x+1; else
    	if (r==1) x=x-1; else
    	if (r==2) y=y+1; else
    	if (r==3) y=y-1;
    }
  }
}
