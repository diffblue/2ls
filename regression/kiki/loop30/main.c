void main() {                                                                     int x;
  __CPROVER_assume(x==0);
  do
  {
    x += 1;
    assert(x<5);
  }        
  while(x<10);                           
} 
