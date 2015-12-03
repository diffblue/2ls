int z;

int f(int i)
{
  z=1;
  return i;
}

void main()
{
  int i, j;
  j=f(i);
  
  // should pass, due to postcondition of f
  assert(j==i);
  assert(z==1);
} 

