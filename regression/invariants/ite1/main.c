void main()
{
  int x;
  int y = 0;
  
  while(y==0) //need to distinguish first iteration
  {
    if(x>=5) y=x;
    else y=5;
  }

  assert(y>=5);
}
