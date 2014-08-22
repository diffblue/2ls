#define SIZE 10

void foo(int a[])
{
  for(unsigned i=0;i<SIZE;i++) a[i] = 0;
}


void main (void)
{
  unsigned a[SIZE];
  foo(a);
}
