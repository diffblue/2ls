int glob;

void my_f(int parameter)
{
  if(parameter>=0)
  {
    assert(parameter==1);
    assert(glob==2);
  }
}
