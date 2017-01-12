int main() {
  int x, y; //, c;
  _Bool c;
  __CPROVER_assume(0 <= x && x <= 3);
  if(c) 
    x-=4;
  else
    x++;     
  assert(x<0);
}

