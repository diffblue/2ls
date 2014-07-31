void foo(int *x) 
{ 
  x++;
  *x = 10;
}

void main()
{
  int x[2];
  foo(&x);
  int y = x[1];
  assert(y==10);
}

