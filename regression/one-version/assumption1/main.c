int main()
{
  int x, i, y;
  
  __CPROVER_assume(x==y);
  
  x++;
  y++;
  
  assert(x==y);
}
