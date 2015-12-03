void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: assert(0);
  }
  return;
}

int x=0;

void eval(void) 
{
  while (1) {
      x=0;
      break;
  }
  return;
}


int main() {

  while(1)
  {
    eval();
assert(x==0);    
  }

assert(x!=0);

  return 0;
}
