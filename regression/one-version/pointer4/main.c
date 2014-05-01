int array[100];

int main()
{
  unsigned int *p;
  int index;
  
  // read
  p=array;
  assert(p==array);
  array[1]=1;
  assert(p[1]==1);
  
  // read with index
  if(index>=0 && index<100)
  {
    p=array+index;
    assert(*p==array[index]);
  }
  
  // write
  p=array;
  *(p+3)=3;
  assert(array[3]==3);
}
