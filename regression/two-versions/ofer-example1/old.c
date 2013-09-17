void f(char b, int x, int y) {
 while (b) {
   x++;
   y++;
  }
  assert(x == y);
}


void main() {
 char b;
 int x,y;
 f(b, x, y);

}
