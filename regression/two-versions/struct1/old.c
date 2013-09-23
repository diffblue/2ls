struct my_S
{
  int a, b, c;
} x;

void f()
{
  assert(x.a==x.b);
}
