int random();

void random1d(int max) {
  int a,x;
  if (max>0) {
  a=0;
  x=1;
  while (x<=max) {
    if (random()) a=a+1; else a=a-1;
    x=x+1;
  }
  }

}
