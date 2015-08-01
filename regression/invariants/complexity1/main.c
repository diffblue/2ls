void main()
{
  unsigned n;
  __CPROVER_assume(n > 0);   // To keep division well defined

  int total = 0;
  unsigned int i = 0;

  unsigned int aux = i / n;

  assert(aux <= 1);

  for (i = 0; i < n; ++i, aux = i / n) {
    assert(aux <= 1);
  }
  
  assert(aux <= 1);
}
