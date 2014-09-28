void speedpldi4(int m, int n){
  int i;

  if(m <= 0) return;
  if(n <= m) return;
  i=n;
  while(i>0)
    if(i<m)
      --i;
    else
      i -= m;
}
  
