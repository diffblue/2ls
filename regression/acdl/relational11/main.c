int main()
{
  signed x,y;
  int d, g;
  if(x==y) {
    if(x<0)
      d=-x;
    else 
      d=x;  
    if(y<0)
      g=-y;
    else 
      g=y;
  }
  else if(x==-y) {
    if(x<0)
      d=-x;
    else 
      d=x;  
    if(y<0)
      g=-y;
    else 
      g=y;
  }
  else { d=g;}
  assert(d==g);
}

