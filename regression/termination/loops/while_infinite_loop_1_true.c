void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: goto ERROR;
  }
  return;
}

int main() {
  int x=0;

  while(1)
  {
    __VERIFIER_assert(x==0);
  }

  __VERIFIER_assert(x!=0);
}
