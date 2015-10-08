extern void __VERIFIER_error() __attribute__ ((__noreturn__));

extern int __VERIFIER_nondet_int(void);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: __VERIFIER_error();
  }
  return;
}
extern unsigned int __VERIFIER_nondet_uint();

void main()
{
  int x;
  if(x!=0) return;
  ++x;
  __VERIFIER_assert(x!=1);
}
