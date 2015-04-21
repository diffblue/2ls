struct some_struct
{
  int b, c, d;
};

int main()
{
  struct some_struct my_s, *p;
  int *q;

  // read through pointer
  p=&my_s;
  my_s.b=1;
  __CPROVER_assert(p->b==1, "p->b");
  
  // write through pointer
  p->c=1;
  __CPROVER_assert(my_s.c==1, "my_s.c");
}
