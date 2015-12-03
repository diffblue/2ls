#define SIZE 3

void main (void)
{
  unsigned a[SIZE] = {0, }; //without initializtion a[i] for i>0 are not initialized in the 1st iteration, and hence we cannot do better than UINT_MAX for the upper bounds

  for(unsigned i=0; i<SIZE; i++) 
    a[i] = i+1;

  assert(a[0]==1);
  assert(a[1]<=SIZE); 
  assert(a[2]<=SIZE); //fails with binary search (may actually also fail with enumeration, if different models were produced). The problem is that for 0<=i<=3, the solver might return a model with i=1, then a[i] = i+1 leaves a[2] unbounded. The template should include a guard that forces an update of a[2] only to happen if the index expression i is equal to 2, what requires knowledge about the index expressions used in assignments...
}
