int main()
{
  int i;

  // jump into the loop  
  goto label;
  
  while(i!=100)
  {
  label:;
  }
  
  assert(0); // unsafe
}
