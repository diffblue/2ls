int main(void) {
  unsigned int x, y;

  while (x > 0) {
    y = x;
    x = 0;

    while (y > 0) {
      y--;
      x++;
    }

    x--;
  }
  assert(x==0);
}
