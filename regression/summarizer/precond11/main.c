void foo(int x) 
{ 
  assert(x!=10);
  assert(x!=11);
  assert(x!=12);
}


int main(int argc, char** argv)
{
  foo(argc);
  return 0;
}
