unsigned f(unsigned y)
{
  unsigned x;
  for(x=0; x<10; x+=y);
  return x;
}

void main()
{
  unsigned z;
  z = z/2 + 1;
  unsigned r = f(z);
}
