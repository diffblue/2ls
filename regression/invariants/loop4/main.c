void main()
{

  int x = 0;
  int y;
  __CPROVER_assume(10<=y && y<=20);

  while(x!=15)
  {
    if(x>0) x=y;
    if(x==0) x=5;
  }

  assert(x>=5);
  assert(x<=20);
}
