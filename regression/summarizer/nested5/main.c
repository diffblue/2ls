#define N 5

void main()
{
int n;
__CPROVER_assume(0<=n && n<=N);
int cost0 = 0;
for(int i=0;i<n;i++) 
{ 
  int cost1 = 0;
  for(int j=0;j<n;j++) 
  {
    int cost2 = 0;
    for(int k=0;k<n;k++) 
    {
      cost2++;
    }
    assert(cost2<=N);
    cost1 += cost2;
  }
  assert(cost1<=N*N);
  cost0 += cost1;
}

assert(cost0<=N*N*N);
}
