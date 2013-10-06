int g();

void f(unsigned l, int x, int y) {
  while (l) {
    l--;
    x++; 
    y--; // note the --. It should fail it.
  }

  assert(x == y);  // this should fail.
}
