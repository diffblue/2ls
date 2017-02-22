int main() {
  int x,y,z;  
  __CPROVER_assume(x==y && y==z && -10<=x && x<0);

//  while(1)
  while(x<=z+2)
  {
//    __CPROVER_assume(x<=z+2);
    z = -y;
    y = -x;
    if(nondet()) x = x+1;
    if(x>=10) {
      x = y = z = 0;
    }
//    if(x>z+2) break;
//    assert(x<=z+2);
  }
  assert(0); //this works with assertion hoisting
}
