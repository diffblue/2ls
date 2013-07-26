int main()
{
  unsigned int x, y;
  
  __CPROVER_assume(x>=1 && x<=3);
  __CPROVER_assume(y<=2);

  // should be both SAT  
  assert(x!=2);
  assert(y!=x);
}
