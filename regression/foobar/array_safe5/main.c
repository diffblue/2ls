#define SIZE 5

void main (void)
{
  unsigned a[SIZE] = {0, }; //without initializtion a[i] for i>0 are not initialized in the 1st iteration, and hence we cannot do better than UINT_MAX for the upper bounds

  for(unsigned i=0; i<SIZE; i++) 
    a[i] = i+1;

  assert(a[0]==1);
  assert(a[1]<=SIZE); 
  assert(a[2]<=SIZE);
  assert(a[3]<=SIZE);
  assert(a[4]<=SIZE);
}
