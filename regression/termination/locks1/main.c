char lock = 0;
char exit = 0;

int acquire_lock(char tid)
{
  if(lock==0) {
    lock=tid;
    return 1;
  }
  return 0;
}

void release_lock() 
{
  lock = 0;
}

void thread1()
{
  if(acquire_lock(1))
  {
    //do_stuff1();
    exit=1; 
    release_lock();
  }
}

void thread2()
{
  if(acquire_lock(2))
  {
    //do_stuff2();
    exit=0;
    release_lock();
  }
}

void main()
{
  while(1)
  {
    thread1();
    thread2();
    if(exit==0) break;
  }
}
