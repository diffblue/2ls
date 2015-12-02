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
    cost1++;
  }
  assert(cost1<=N);
  cost0 += cost1;
}

assert(cost0<=N*N);
}
