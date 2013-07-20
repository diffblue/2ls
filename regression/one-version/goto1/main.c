int main()
{
  int x, i, y;
  
  y=1;
  
  switch(i)
  {
  case 1: goto l1;
  case 2: goto l2;
  case 3: goto l3;
  case 4: goto l4;
  default: return 0;
  }
  
  l1: x=1; goto check;
  l2: x=y; goto check;
  l3: x=1; goto check;
  l4: x=1; goto check;

  check:
  assert(x==1);
}
