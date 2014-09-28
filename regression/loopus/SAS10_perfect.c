int perfect(int x){
  int y1, y2, y3;

  if(x <= 1) return 0;

  y1=x;
  y2=x;
  y3=x;

  for(y1 = x-1; y1>0;y1=y1-1){
    while(y2 >= y1) y2 = y2 - y1;
    if(y2 == 0)
      y3 = y3 - y1;
    y2 = x;
  }

  return (y3 == 0);
}
