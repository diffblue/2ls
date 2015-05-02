int array[10000];

int main()
{
  int *p;
  int index;
  
  // read
  p=array;
  assert(p==array);
  array[1]=10;
  p++;
  assert(p[0]==10);

  // read with index
  if(index>=0 && index<10000)
  {
    p=array+index;
    assert(*p==array[index]);
  }
  
  // write
  p=array;
  *(p+3)=3;
  assert(array[3]==3);
}
