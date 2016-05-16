int my_global;

int f(void)
{
  my_global=4;
  return 2;
}

int main()
{
  int i=1;
  my_global=3;
  
  i=f();
  
  // check that 'i' is assigned, i.e., should fail
  assert(i==1);

  // check that 'my_global' is assigned, i.e., should fail
  assert(my_global==3);

  return 0;
}

