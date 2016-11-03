int abs(int x) {
  return (x < 0 ? -x:x);
}
int main()
{
  unsigned x,y,z;
  __CPROVER_assume(x>=-10 && x<=10); 
  if(x==y) 
   z = abs(x) - abs(y);
  else if(x==-y)
   z = abs(x) - abs(y);
  assert(z==0);
}

