int main()
{
  signed x,y;
  int d, g;
  __CPROVER_assume(x==y || x==-y);
  
  if(x<0)
    d=-x;
  else 
    d=x;  
  if(y<0)
    g=-y;
  else 
    g=y;
  
  assert(d==g);
}

