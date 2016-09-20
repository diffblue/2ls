int main()
{
  unsigned x,y,z;
  
  __CPROVER_assume(x==y || x==-y);
  z = abs(x) - abs(y);
  
  assert(z==0);
}

