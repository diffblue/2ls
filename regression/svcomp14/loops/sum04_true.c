void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: assert(0);
  }
  return;
}
#define a (2)
#define SIZE 8
int main() { 
  int i, sn=0;
  for(i=1; i<=SIZE; i++) {
    sn = sn + a;
  }
assert(sn==SIZE*a || sn == 0);
}

