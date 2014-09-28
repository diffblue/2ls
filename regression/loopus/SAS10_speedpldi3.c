void speedpldi3(int m, int n){
  int i, j;
  if(m <= 0) return;
  if(n <= m) return;
  i=0;
  j=0;
  while(i<n)
    if(j<m) ++j;
    else {
      j = 0;
      ++i;
    }
}
