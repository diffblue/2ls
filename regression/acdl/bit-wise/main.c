struct data {
  unsigned int x, y;
};
struct data d;

int main() {
  d.x = 5;
  d.y = (d.x << 2)&0xf;
  // d.y should be 4
  assert(d.y != 4);
}
