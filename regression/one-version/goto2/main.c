int main()
{
  int x, i;
  
  switch(i)
  {
  case 1: goto l1;
  case 2: goto l2;
  case 3: goto l3;
  case 4: goto l4;
  default: return 0;
  }
  
  l1: x=1; goto check;
  l2: x=2; goto check;
  l3: x=1; goto check;
  l4: x=1; goto check;

  check:
  // should fail
  assert(x==1);
}
