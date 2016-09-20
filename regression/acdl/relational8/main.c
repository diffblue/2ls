int main()
{
  unsigned x,y,z;
  
  if(x==y) 
   z = abs(x) - abs(y);
  else if(x==-y)
   z = abs(x) - abs(y);
  assert(z==0);
}

