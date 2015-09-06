void main()
{
  int y = 5;
  int i;
  for(i=0; i<10; i+=y)
    {
      int y = 20;
    }
  assert(y==5);
  assert(i==10);
}
