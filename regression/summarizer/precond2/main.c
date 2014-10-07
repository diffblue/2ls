void foo(int x) 
{ 
  int y = x;
  assert(y>=10);
}

int main(int argc, char** argv)
{
  foo(argc);
}
