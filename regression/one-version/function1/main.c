int f(void)
{
  return 2;
}

int main()
{
  int i=1;
  i=f();
  
  // check that 'i' is assigned, i.e., should fail
  assert(i==1);
} 

