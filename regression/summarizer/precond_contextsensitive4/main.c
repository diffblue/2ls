
int sign(int x) 
{ 
  if(x>0) return 1;
  else if (x==0) return 0;
  return -1;
}

int main(int argc, char** argv)
{
  int x = argc-1;
  //assert(!(x <= 0 && -((signed __CPROVER_bitvector[33])x) <= 0));
  int y = sign(x);
  assert(y!=0);
  return 0;
}

