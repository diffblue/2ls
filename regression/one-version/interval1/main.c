int main()
{
  unsigned int x, y;
  
  __CPROVER_assume(x>=1 && x<=3);
  __CPROVER_assume(y<2);
  
  // should be both UNSAT
  assert(x!=4);
  assert(y<=1);
  
  return 0;
}
