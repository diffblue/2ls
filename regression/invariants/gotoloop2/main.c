void main()
{
  int x,y;
  if(x<-5) goto LOOP;
  
  x = 0;
  while(x<10)
  {
    x++;
    LOOP:
    if(x>7) continue;
    if(x>9) break;
    x++;
  }
  assert(x==10);
}
