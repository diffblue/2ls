unsigned f(unsigned x) 
{ 
  x=x+1;
  return x;
}

unsigned g(unsigned x) 
{
  x++; 
  return x;
}

int main()
{
  unsigned x;
  assert(f(x) == g(x));
}

