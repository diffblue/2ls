void wise(int x, int y){
  if(x<0 || y<0) return;
  while(x-y>2 || y-x>2)
    if(x < y) ++x;
    else ++y;
}
