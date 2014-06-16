int foo(int x, int y) 
{ 
  int res = y;
  //if(x) res = 0;
  return res;
}
int bar(int x) 
{   
  int res = 2;
  //if(x) res = 1;
  return res; 
}

void doit(int x)
{
  int y = 0;
  int z = bar(x);
  x++;
  assert(foo(x,y)<=z);
}

void entry()
{

  int x;
  int y;
  
  if(x>=5)
  {
    y=x;
  } else
  {
    y=5;
  }
  
  y=y;
  
  assert(y>=5);
}

function to be analyzed: 
(E) $cond#31 == TRUE
(E) y#30 == x#27
(E) $guard#30 == ($guard#27 && !$cond#29)
(E) $guard#27 == TRUE
(E) $cond#29 == !(x#27 >= 5)
(E) y#32 == 5
(E) $guard#32 == !(x#27 >= 5) 
(E) y#phi33 == ($guard#32 ? y#32 : y#30)
(E) y#33 == y#phi33
(E) $guard#33 == ($guard#30 && $cond#31 || $guard#32 && TRUE)

