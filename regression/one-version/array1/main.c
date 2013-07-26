int main()
{
  long int i;
  char my_buffer[1000];
  
  if(i>=0 && i<1000)
  {
    my_buffer[i]=0; // should pass
  }
  else
    my_buffer[i]=1; // should fail
}
