int main() {
  int x=0, y, y0;
  __CPROVER_assume(y>=5); // && y<=6);
  y0 = y;
  while(x<y) {
    x++; y-=2;
  }
  assert(2*x<y0);
}
