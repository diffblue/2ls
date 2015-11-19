

int main(int argc, char** argv)
{
  short size = 5;
  char s[size];
  for(int i=0; i<size; i++)
    s[i] = 1;
  assert(s[size-1]==1);
}
