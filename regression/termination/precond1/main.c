int foo(int y)
{
  int x=0;
//  if(0<=y && y<=5)
  {
    for(; x<10; x+=y);
    //assert(y!=0);
  }
  return x;
}

int main(int argc, char** argv)
{
  int y = argc;
  return foo(y-1);
}

