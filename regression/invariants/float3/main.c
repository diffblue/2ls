void main()
{
  float x = 10.0;  

  while(x>0) // does not terminate
  {
    x = x*0.1 + 0.1;
    assert(x!=0.0);
  }
  assert(x>=0.0);
}
