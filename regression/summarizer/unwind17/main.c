void main()
{
  int x, z, w;  
  __CPROVER_assume(x>=0);
  int y = 0;

  while(x>0)
  { 
    if(z)  y = y + x;
    else break;
    x++;
    if(w) x--;
    else break;
    x -= 3;
  }

  assert(x>=-4);
}
