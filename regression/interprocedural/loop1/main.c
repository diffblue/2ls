int x=0;

void eval(void) 
{
  while (1) {
    x=1;
    break;
  }
  return;
}

int main() {

  int N;
  int i=0;
  while(i++<N)
  {
    eval();
  }

  assert(x>=0);

  return 0;
}
