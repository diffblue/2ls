int main()
{
  long int i, j;
  char my_buffer[10];
  
  // constant index
  my_buffer[1]=1;
  my_buffer[2]=2;
  assert(my_buffer[1]==1);
  assert(my_buffer[2]==2);
  
  // variable index
  if(i>=0 && i<10 && j>=0 && j<10)
  {
    my_buffer[i]=1;
    assert(my_buffer[i]==1);
    my_buffer[j]=2;
    assert(my_buffer[j]==2);
    if(i!=j) assert(my_buffer[i]==1);
  }
}
