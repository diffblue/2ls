void f(int i)
{
  if(i == 1)
    assert(0);  // this should not fail, due to calling context
}

void main()
{
  int i = 2;
  f(i);
} 

