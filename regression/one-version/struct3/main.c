struct some_struct
{
  int n;
};

void func(struct some_struct *my_ptr)
{
  assert(my_ptr->n==42);
}

int main()
{
  struct some_struct local_struct = { .n = 42 };

  func(&local_struct);
  
  return 0;
}
