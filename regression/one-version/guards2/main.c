int main()
{
  int i, j, k;

  __CPROVER_assume(i==10);
  
  k=100;
  
  while(j!=10)
  {
  }
  
  __CPROVER_assert(i==10, "i");
  __CPROVER_assert(j==10, "j");
}
