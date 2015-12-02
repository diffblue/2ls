void main() {                                                                     int x;
  __CPROVER_assume(x==4);
  while(x>0)
  {
    int y;
    __CPROVER_assume(-3<=y && y<=-1);
    x += y;
  }        
  assert(x==0 || x==-2);                           
} 
