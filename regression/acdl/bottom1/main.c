int main() {
  int x, y;

  x = 1;
  assert(x!=0);
}

/*
(E) $guard#0 == TRUE
(E) x#17 == 1
(A) !$guard#0 || x#17 != 0
*/
