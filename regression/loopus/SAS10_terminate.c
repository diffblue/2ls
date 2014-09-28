void terminate(int i, int j, int k){
  int ell;
  while(i <= 100 && j <= k){
    ell = i;
    i = j;
    j = ell+1;
    k--;
  }
}
