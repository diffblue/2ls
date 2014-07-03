#define LIMIT 2

int a[LIMIT];

void pass_through_array ()
{
  for(unsigned i=0; i<LIMIT; i++)
    a[i] = a[i];
}

void main (void) {

  a[0] = 0;
  a[1] = 0;

  pass_through_array();
  
  assert(a[0] == 0 && a[1] == 0);
}
