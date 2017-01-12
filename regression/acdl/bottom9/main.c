int main() {
 unsigned x, y;
 __CPROVER_assume(x==y);
 x++; y++;
 x++; y++;
 assert(x==y);
}
