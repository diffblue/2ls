void my_f(int *parameter)
{
  parameter[10]=1;
}

struct S
{
  struct S *n;
  int payload;
};

int i;

void my_g(struct S *p)
{
  i++;
  p->n->n->payload=1;
}
