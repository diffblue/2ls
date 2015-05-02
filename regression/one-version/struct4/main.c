struct some_struct
{
  int a, b, c, d;
  
  struct nested
  {
    int e, f;
  } sub;
};

int main()
{
  struct some_struct my_s, *p;
  int *q;
  char *char_p=0;

  // read through pointer
  p=&my_s;
  my_s.b=1;
  __CPROVER_assert(p->b==1, "p->b");
  
  // write through pointer
  p->c=2;
  __CPROVER_assert(my_s.c==2, "my_s.c");
  
  // pointer into struct
  q=&p->d;
  my_s.d=3;
  __CPROVER_assert(*q==3, "q 3");

  // pointer into sub-struct
  q=&p->sub.e;
  my_s.sub.e=4;
  __CPROVER_assert(*q==4, "q 4");

  return 0;
}
