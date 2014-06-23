int main()
{
  int i, j;

  __CPROVER_assume(i!=10);
  
  while(j!=10)
  {
  }
  
  assert(i==10);
  assert(j==10);  
}
