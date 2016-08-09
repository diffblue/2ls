int main() {
 unsigned x, y;
 __CPROVER_assume(x==y);
 assert(x!=y);
}
