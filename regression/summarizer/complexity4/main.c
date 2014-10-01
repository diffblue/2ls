void main()
{
  unsigned char n;
  __CPROVER_assume(n > 0);   // To keep division well defined
  __CPROVER_assume(n * n > 0);   // To keep division well defined

  unsigned char i = 0;
  unsigned char j = 0;

  unsigned char aux1 = i / (n * n);
  unsigned char aux2 = j / n;

  assert(aux1 <= 1);
  assert(aux2 <= 1);

  for (i = 0; i < n; ++i, aux1 = i / (n * n)) {
    for (j = 0; j < n; ++j, aux2 = j / n) {

      assert(aux1 <= 1);
      assert(aux2 <= 1);
    }

    assert(aux1 <= 1);
    assert(aux2 <= 1);
  }

/*  aux1 = i / (n * n);
    aux2 = j / n; */

  assert(aux1 <= 1);
  assert(aux2 <= 1);
}
