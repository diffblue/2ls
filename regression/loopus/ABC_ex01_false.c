int nondet();

void ex01(int a, int b) {
  while (a >= b) { //does not terminate if a == MAX_INT
    b = b + 1;
  }
  return;
}
void main() {}
