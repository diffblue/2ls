int x, y, z;

int main()
{
  // does not require invariant, just exit condition
  for(x=0; x!=100; x++);
  assert(x==100);
  
  // same again with do-while
  y=0;
  do y++; while(y!=100);
  assert(y==100);
  
  // Same again with a 'break', but this is basically
  // the same CFG as the first one.
  z=0;
  while(1) { if(z==100) break; z++; }
  assert(z==100);
  
  return 0;
}
