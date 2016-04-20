void main()
{
  int x;  

  __CPROVER_assume(5<=x && x<=100);
  for(int y=0;y<5;y++) x++;

  assert(x>=10);
}
