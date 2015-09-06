int g = 1;

void modify_global() 
{
  g = g;
}

void main()
{
  int x;

  //g = g;

  if(x) 
  {
     modify_global(); 
  }

  modify_global(); 

  assert(g==1);
}

