unsigned f(unsigned x, _Bool op) 
{ 
  if(op)
   x=x+1;
  else
   x=x-1;
  return x;
}

unsigned g(unsigned x, _Bool op) 
{
  if(op)
   x++;
  else
   x--;
  return x;
}

int main()
{
  unsigned x;
  _Bool op;
  assert(f(x,op) == g(x,op));
}

