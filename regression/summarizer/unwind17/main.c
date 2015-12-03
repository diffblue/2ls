void main()
{
  int x, z, w;  
  __CPROVER_assume(x>=0);
  int y = 0;

  while(x>0)
  { 
    x = x;
    if(z)  y = y + x;
    else break;
    x--;
    if(w) break; 
    else x++;
    x -= 3;
  }

  assert(x>=-4);
}
