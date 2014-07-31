#define LIMIT 10

int a[LIMIT];

void pass_through_array ()
{
  for(unsigned i=0; i<LIMIT; i++)
    a[0] = a[0];
}

void main (void) {

  a[0] = 0;
  a[1] = 0;

  pass_through_array();
  
  assert(a[0] == 0 && a[1] == 0);
}
