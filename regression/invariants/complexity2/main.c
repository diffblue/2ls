void main()
{
  unsigned n;
  __CPROVER_assume(n > 0);   // To keep division well defined

  unsigned int i = 0;
  unsigned int cost = 0;

  unsigned int aux = cost / n;

  assert(aux <= 1);

  for (i = 0; i < n; ++i, ++cost, aux = cost / n) {
    assert(aux <= 1);
  }
  
  assert(aux <= 1);
}
