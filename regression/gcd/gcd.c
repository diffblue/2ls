
int nondet_int();

int gcd(int n1, int n2)
{
  while(n1!=n2){
  if(n1>=n2-1)
    n1=n1-n2;
  else
    n2=n2-n1;
  }
  return n1;
}


int main()
{

  int a=nondet_int();
  int b=nondet_int();
  
  __CPROVER_assume(a>0 && b>0);

  int g=gcd(a,b);
  
  return g;
}
