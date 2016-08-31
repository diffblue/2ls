int f(int x) {
 return 2*x;
}

int g(int x) {
  int t=x;
  int y=0;
  for(; x>0; --x) {
    ++y;
  }
  return t+y;
}

void main() {
  int x;
  if(0<=x && x<=10)
    assert(f(x) == g(x));
}

