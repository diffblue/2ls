int nondet_int();

int main()
{
  int Old = 0, New = 0;
  char lock;

  do
  {
    lock = 1;
    Old = New;

    if(nondet_int())
    {
      lock = 0;
      New++;
    }
  }
  while (New != Old);  

  assert(lock == 1);
}

