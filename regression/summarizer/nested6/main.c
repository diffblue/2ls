void main()
{
  int x;
  __CPROVER_assume(x==5);
  int i,j;
  for(i=0; i<x; i++)
  {
    int y;
    __CPROVER_assume(y==100);
    for(j=0; j<y; j+=x);
  }
  assert(i==5);
  assert(100<=j && j<=105);
}
