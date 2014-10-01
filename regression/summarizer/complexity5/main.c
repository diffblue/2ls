void main()
{
  unsigned char n;
  __CPROVER_assume(n > 0);   // To keep division well defined
  __CPROVER_assume(n * n > 0);   // To keep division well defined

  unsigned char i = 0;
  unsigned char j = 0;

  unsigned char cost1 = 0;
  unsigned char cost2 = 0;

  unsigned char aux1 = cost1 / (n * n);
  unsigned char aux2 = cost2 / n;

  assert(aux1 <= 1);
  assert(aux2 <= 1);

  for (i = 0; i < n; ++i, aux1 = cost1 / (n * n)) {
    for (j = 0; j < n; ++j, ++cost2, aux2 = cost2 / n) {

      assert(aux1 <= 1);
      assert(aux2 <= 1);
    }

    cost1 += cost2;
  }

/*  aux1 = cost1 / (n * n);
    aux2 = cost2 / n; */

  assert(aux1 <= 1);
  assert(aux2 <= 1);
}

