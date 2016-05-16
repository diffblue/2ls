void main()
{
  int a = 0;
  int b = 0;
  int x = 0;
  int y = 0;
  while(x<10)
  {
    x++;
    y++;
    if(x==y) a = x;
    if(x==a) b = a; //here transitivity of equalities is needed
  }
  assert(x==b);
}
