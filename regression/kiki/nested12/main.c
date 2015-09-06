#define a 2

extern int nondet_int();

int main() { 
  int i=0, n=3,sn=0,x,y;

  for(x=0;x<5;x++)
  {
    sn = nondet_int();
  
    while(i<n) {
      sn = sn + a;
      i++;
    }
  }
  assert(sn== n*a || sn == 0);
}
