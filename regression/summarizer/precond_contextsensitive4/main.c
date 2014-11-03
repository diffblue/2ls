
int sign(int x) 
{ 
  if(x>0) return 1;
  else if (x==0) return 0;
  return -1;
}

int main(int argc, char** argv)
{
  int x = argc-1;
  int y = sign(x);
  assert(y!=0);
  return 0;
}

