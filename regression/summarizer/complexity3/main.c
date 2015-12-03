void main()
{
  unsigned int n;
  __CPROVER_assume(n > 0);   // To keep division well defined
  __CPROVER_assume(n * n > 0);   // To keep division well defined

  unsigned int i = 0;
  unsigned int j = 0;

  unsigned int cost1 = 0;
  unsigned int cost2 = 0;

  unsigned int aux1 = cost1 / (n * n);
  unsigned int aux2 = cost2 / n;

  assert(aux1 <= 1);
  assert(aux2 <= 1);

  for (i = 0; i < n; ++i, aux1 = cost1 / (n * n)) {
    for (j = 0; j < n; ++j, ++cost2, aux2 = cost2 / n) {

      assert(aux1 <= 1);
      assert(aux2 <= 1);
    }

    cost1 += cost2;
  }

  aux1 = cost1 / (n * n);
  aux2 = cost2 / n;

  assert(aux1 <= 1);
  assert(aux2 <= 1);
}

