int glob;
 
void my_f(int parameter)
{
  int x = 0;
  while (x == 0) {
    x = 1;
  }
  assert(parameter==1);
  assert(glob==2);
}
