void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: assert(0);
  }
  return;
}
_Bool __VERIFIER_nondet_bool();
int __VERIFIER_nondet_int();

//x is an input variable
int x;

void foo() {
  x--;
}

int main() {
  x=__VERIFIER_nondet_int();
  while (x > 0) {
    _Bool c = __VERIFIER_nondet_bool();
    if(c) foo();
    else foo();
  }
assert(x<=0);
}



