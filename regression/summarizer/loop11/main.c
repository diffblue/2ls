void main()
{
  int n;
  __CPROVER_assume(n==0);
  int x = 0;  

  while(x<n)
  {
    ++x;
  }

  assert(x==0);
}
