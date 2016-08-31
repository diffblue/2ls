int main() {
 unsigned x, y;
 __CPROVER_assume(x==y);
 x++;
 assert(x==y+1);
}
