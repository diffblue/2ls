void foo(char* x) 
{ 
  assert(x!=0);
  *x = 0;
}

int main(int argc, char** argv)
{
  assert(argv!=0);
  foo(*argv);
}
