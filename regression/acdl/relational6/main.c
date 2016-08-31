unsigned f(unsigned x, _Bool op) 
{ 
  if(op)
   x=5;
  else
   x=10;
  return x;
}

unsigned g(unsigned y, _Bool op) 
{
  if(op)
   y=5;
  else
   y=10;
  return y;
}

int main()
{
  unsigned x;
  _Bool op;
  assert(f(x,op) == g(x,op));
}

