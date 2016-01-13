int main() {
int x, y;

if(y!=0) {
  x=y;
  assert((y!=0));
}
else
  x=y+5;


/*
 while(nondet_bool())
    x=x+x;
*/
  assert((x!=0));
}
