int foo(int x)
{
  assert(x>=50);
  return x;
}


int main(int argc, char** argv)
{
  __CPROVER_assume(argc>=20);
  return foo(argc);
}

