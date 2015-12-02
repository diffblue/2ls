

int main(int argc, char** argv)
{
  short size = 1;
  char s[size];
  for(int i=0; i<size; i++)
  {
    int y = 2;
    int x;
    if(1 == x) 
      s[i] = x;
    else y = x;
  }
  assert(s[size-1]==1);
}
