
int nondet_int();


int main()
{

  int a=nondet_int();
  int b=nondet_int();
  int n1=a;
  int n2=b; 
 
  __CPROVER_assume(a>0 && b>0);

  while(n1!=n2){
  if(n1>=n2-1)
    n1=n1-n2;
  else
    n2=n2-n1;
  }
  int g=n1;
 
  assert(a % g == 0);
  assert(b % g == 0);

  assert(a % g == 0 && b % g ==0);
  
  return 0;
}
