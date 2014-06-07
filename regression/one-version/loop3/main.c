int main()
{
  int x;
  
  // does not require invariant, just exit condition
  for(x=0; x!=100; x++);
  
  assert(x==100);
  
  return 0;
}
