void main()
{
  int x = 0;  

  while(x<10)
  {
    ++x;
//    if(x%2) continue;
//    ++x;
    assert(x<=10);
  }
//  x = x;
  assert(x==10);
}
