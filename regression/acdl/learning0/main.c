int main() 
{
  unsigned x,y,z;
  
  // ************* Test for Intervals *********** // 
  
  // Decision: x<=2 -- PASSED
  //__CPROVER_assume(x>2 && z==x+4 && y==(x+z)/2);
  // Decision: x+y<=4 -- PASSED
  //__CPROVER_assume(x+y>4 && z==x+4 && y==(x+z)/2);
  __CPROVER_assume(x+y>4);
  //__CPROVER_assume(x>2);
  z=x+4;
  y=(x+z)/2;

  assert(y+z<=10);
}
