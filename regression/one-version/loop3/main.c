int x, y;

int main()
{
  // does not require invariant, just exit condition
  for(x=0; x!=100; x++);
  assert(x==100);
  
  // same again with do-while
  y=0;
  do y++; while(y!=100);
  assert(y==100);
  
  return 0;
}
