struct my_S_new
{
  int a, b, c;
} x;

void f()
{
  assert(x.a==x.b);
}
