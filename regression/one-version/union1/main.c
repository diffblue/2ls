union my_U
{
  char array[sizeof(int)];

  int i;

  struct S
  {
    char ch0, ch1, ch2, ch3;
  } s;
};

int main()
{
  union my_U u;
  
  assert(u.array[0]==u.s.ch0);
  assert(u.array[1]==u.s.ch1);
  assert(u.array[2]==u.s.ch2);
  assert(u.array[3]==u.s.ch3);

  u.i=0x04030201;
  
  if(u.s.ch0==0x01)
  {
    // little endian
    assert(u.s.ch1==0x02 && u.s.ch2==0x03 && u.s.ch3==0x04);
  }
  else
  {
    // big endian
    assert(u.s.ch1==0x03 && u.s.ch2==0x02 && u.s.ch3==0x01);
  }
}
