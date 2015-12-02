void main()
{
  int x,y;
  if(x<-5) goto LOOP;
  
  x = 0;
  while(x<10)
  {
    x++;
    LOOP:
    x++;
  }
  assert(x==10 || x==11);
}
