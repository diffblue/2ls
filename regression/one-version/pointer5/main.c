int i;

int main()
{
  // 'open' pointers
  int *p, *q;

  *p=1;
  assert(*p==1);
  
  if(p==q)
    assert(*q==1);

  i=100;
  *q=2;
  
  if(p==q)
    assert(*p==2);

  // aliasing with other stuff    
  if(q==&i)
    assert(i==2);
  else
    assert(i==100);
}
