int main()
{
  int i, j, k;

  __CPROVER_assume(i!=10);
  
  k=100;
  
  while(j!=10)
  {
  }
  
  assert(i==10);
  assert(j==10);  
}
