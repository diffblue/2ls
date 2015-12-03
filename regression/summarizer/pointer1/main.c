void foo(int *x) 
{ 
  *x = 10;
}

void main()
{
  int x;
  foo(&x);
  assert(x==10);
}

