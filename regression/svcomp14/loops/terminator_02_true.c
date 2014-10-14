extern void __VERIFIER_assume(int);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: assert(0);
  }
  return;
}
int __VERIFIER_nondet_int();
_Bool __VERIFIER_nondet_bool();

main()
{
  int x=__VERIFIER_nondet_int();
  int y=__VERIFIER_nondet_int();
  int z=__VERIFIER_nondet_int();
__CPROVER_assume(x<100);
__CPROVER_assume(z<100);
  while(x<100 && 100<z) 
  {
    _Bool tmp=__VERIFIER_nondet_bool();
    if (tmp)
   {
     x++;
   }
   else
   {
     x--;
     z--;
   }
  }                       
    
assert(x>=100 || z<=100);
}


