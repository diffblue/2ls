#define a 2

extern int nondet_int();

int main() { 
  int i=0, n=3;

  int sn0 = nondet_int();
  int sn = sn0;
  
  while(i<n) {
    sn = sn + a;
    i++;
  }
  assert(sn == sn0+n*a);
}
