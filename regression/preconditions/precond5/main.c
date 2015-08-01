int foo(int len, int *a) 
{ 
  if(len>=0)
  {
    assert(len>=3);
    return a[2];
  }
  return -1;
}

int main(int argc, char** argv)
{
  int a[5] = {0,0,0,0,0};
  int len = 5;
  int y = foo(len,a);
  assert(y>=0);
}
