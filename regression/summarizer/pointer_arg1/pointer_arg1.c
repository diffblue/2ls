int foo(int *x)
{
  int y = *x;
  return y;
}

int main(int argc, char** argv)
{
  int a;
  int *b;
  int c;
  if(c) b = &argc;
  else b = &a;
  int d = foo(b);
  assert(d==argc || d==a);
}
