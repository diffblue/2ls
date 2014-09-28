// while 2 = ex multidim du papier !
// utiliser -noaccel sinon bug
int while2(int N){

  int i,j;
  i=N;
  while(i>0) {
    j=N;
    while(j>0)j--;
    i--;
  }
  return 0;
}
