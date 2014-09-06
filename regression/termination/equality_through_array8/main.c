int a[3];
int b[3];

void main (void) {
  a[0] = 1;
  a[1] = 2;
  a[2] = 3;

  for(unsigned i=0; i<3; i++)
    b[i] = a[i];
  
  assert(b[0] == 1 && b[1] == 2 && b[2] == 3);
}
