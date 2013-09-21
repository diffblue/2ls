int global;

int main()
{
  int *p;
  
  p=&global;
  global=1;
  assert(global==1);
  *p=2;
  assert(p==&global);
  assert(global==2);  
}
