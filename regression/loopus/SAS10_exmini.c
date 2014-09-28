/*exmini*/

int exmini(int i, int j, int k)
{
  int tmp;

  while(i<=100 && j<=k){
    tmp = i;
    i=j;
    j=tmp+1;
    k=k-1;
  }


  return 0;

}
