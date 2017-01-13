int main()
{
  unsigned x,y;
  __CPROVER_assume(x>=1 && x<=5);
  _Bool c;
  if(c)
    y=2*x-1;
  else
    y=2*x-2;
  assert(y<=2*x);
}

