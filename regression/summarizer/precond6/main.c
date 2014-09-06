void foo(int x) 
{ 
  int y = x;
  assert(y>=0);
}

int main(int argc, char** argv)
{
  foo(argc);
}
