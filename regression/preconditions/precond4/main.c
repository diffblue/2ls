int FirstOccurrence(int len, int a[]) 
{ 
  if(len<=0) return -1;
  int i = 0;
  assert(i<len);
  while(a[i]!=3) 
  {
    i++;
    assert(i<len);
  }
  return i;
}

int main(int argc, char** argv)
{
  int a[5] = {0,0,0,0,0};
  int x = FirstOccurrence(5,a);
  assert(x>=0);
}
